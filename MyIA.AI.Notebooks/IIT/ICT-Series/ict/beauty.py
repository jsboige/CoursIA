"""Le brin Schmidhuber de la jambe K : beaute comme **gain local de
compressibilite** (strate 5, Epic #4588, See #5090).

La theorie fondatrice (cadrage ICT-0) pose trois jambes -- integration (Phi),
surprise (F), compression (K) -- comme trois facettes d'un meme quantite.
``compression`` (ICT-15) a attache la jambe K a la **trajectoire** via la courbe
de Schmidhuber. Ce module en tire la consequence que Schmidhuber appelle
**beaute subjective / curiosite** : un evenement esthetique est un **saut de
compressibilite**, le moment ou une histoire jusque-la incompressible devient
soudain compressible (la decouverte d'une regle, d'un attracteur, d'une
symetrie). C'est la *derivee* de la compressibilite, non son niveau, qui porte
le signal esthetique.

Le brin Thom (couche 1) pose en outre que ce saut a la geometrie d'une
**catastrophe** : la compressibilite ne glisse pas douce­ment, elle *bascule*
entre deux bassins (exploration incompressible / exploitation compressible).
C'est le meme pli que ``catastrophe.fold_lines``, transplante dans l'espace 1D
de la courbe de compressibilite. Le module ``catastrophe`` fournit la fronce ;
``compression`` fournit le compresseur ; ``beauty`` les croise.

Méthodologie operationnelle (validée empiriquement, voir tests B1-B4)
----------------------------------------------------------------------

Deux choix honnetes, contre-intuitifs, motivés par l'expérience :

1. **Fenêtre glissante locale, pas préfixe accumulé.** ``compression_progress``
   rapporte la compressibilité de l'histoire *accumulée*
   (``len(prefix[:t]) / len(prefix[:t-W])``). Verifié empiriquement : ce ratio
   reste ~1.0 meme pour une transition nette bruit->cycle, car l'historique
   incompressible accumulé dilue toute structure locale ajoutée. Il est donc
   **trop grossier pour detecter une découverte en milieu de séquence**. On
   mesure à la place la compressibilité d'une fenêtre glissante
   ``local_K[t] = compressed_length(states[t-W:t])`` : le signal LOCAL,
   sensibles au moment où le passe recent devient compressible. C'est la
   bonne opérationalisation de Schmidhuber (« compressibilité de l'expérience
   récente »).

2. **Contrôle iid apparié, pas permutation.** ``compression_gain`` contrôle par
   permutation (préserve les fréquences, detruit l'ordre) -- adapté pour
   créditer la structure d'ordre *totale*. Mais pour un détecteur LOCAL de
   découverte, la permutation est **trop faible** : elle préserve la composition
   en segments hétérogènes, donc « découvre » elle aussi des fenêtres
   compressibles par clustering aleatoire. On contrôle à la place par un **iid
   apparié** (même longueur, même taille d'alphabet) : le null « aucune
   structure temporelle apprenable ».

Le détecteur :

* ``local_K[t] = compressed_length(states[t-W:t])`` (fenêtre pleine).
* lissage par moyenne mobile centrée en mode ``valid`` (anti effet de bord --
  le ``mode='same'`` produit des courbures artificielles aux bords qui
  declenchent de faux plis).
* ``delta[t] = smoothedK[t-horizon] - smoothedK[t]`` : gain de compressibilité
  sur l'horizon (positif = la fenêtre récente se compresse mieux).
* seuil ``mean(ctrl_max) + k * std(ctrl_max)`` sur le **max** du contrôle iid
  (le max d'une courbe est positivement biaisé -> il faut centrer le seuil sur
  la moyenne du null, pas sur 0). ``k=2.5`` par défaut.
* evenements = maxima locaux de ``delta`` au-dessus du seuil (peak-picking ->
  une découverte = un evenement au pic, pas toute la rampe).

Trois gates falsifiables (``tests/test_beauty.py``) :

* **B1** bruit iid puis cycle deterministe -> >=1 evenement au voisinage de la
  transition.
* **B2** bruit iid pur -> aucun evenement (sous le seuil iid).
* **B3** cycle deterministe depuis le debut -> aucun evenement (compressible
  partout, pas de saut).

Sans complaisance : zlib niveau 9 est un estimateur BRUT de K (pas de modele
MDL explicite, cf ICT-16). La fenêtre ``W`` doit etre assez large (>= ~40
elements pour un alphabet de 4 symboles) pour que la variance de
quantification zlib soit negligeable devant le signal de découverte ; sur des
fenêtres trop courtes le détecteur est bruité (documenté, non maquillé). Le
notebook ICT-26 (a venir) testera la robustesse au compresseur (LZMA, PPM) et la
convergence avec les Gates Phi/F/K sur des trajectoires reelles.

Dependances : ``compression`` (``compressed_length``, ``canonical_int_sequence``)
+ ``numpy``. Aucune dependance a ``catastrophe`` a l'import.
"""

from __future__ import annotations

import math
from typing import List, Optional, Sequence, Tuple

import numpy as np

from .compression import canonical_int_sequence, compressed_length


# --------------------------------------------------------------------------- #
#  Courbe de compressibilite locale (fenêtre glissante)                       #
# --------------------------------------------------------------------------- #


def local_compressibility(
    states: Sequence, window: int, level: int = 9
) -> Tuple[np.ndarray, np.ndarray]:
    """``local_K[t] = compressed_length(states[t-window:t])`` sur fenêtres pleines.

    Renvoie ``(steps, K)`` ou ``steps[t] = window + t`` (le pas d'arrivee de la
    fenêtre) et ``K[t]`` est la longueur zlib de la fenêtre pleinement remplie.
    On n'empiete pas sur le debut (pas de fenêtre tronquee) : cela evite la
    derive artificielle des premiers pas et garde la courbe homogene.

    La compressibilité est une mesure **locale** de K : basse = fenêtre
    compressible (structure detectee), haute = fenêtre incompressible
    (exploration / bruit). C'est le signal brut dont on tire la derivee
    « beauté ».
    """
    if window < 1:
        raise ValueError(f"window doit etre >= 1, recu {window}")
    seq = list(states)
    steps = np.arange(window, len(seq) + 1, dtype=float)
    K = np.array(
        [compressed_length(seq[t - window:t], level=level) for t in range(window, len(seq) + 1)],
        dtype=float,
    )
    return steps, K


def smooth_curve(values: np.ndarray, half: int) -> np.ndarray:
    """Moyenne mobile centree, mode ``valid`` (pas d'effet de bord).

    ``half`` = demi-largeur (fenêtre ``2*half+1``). Le mode ``valid`` reduit la
    sortie de ``2*half`` points ; c'est voulu -- les bords d'une convolution
    ``same`` produisent des courbures artificielles qui declenchent de faux
    plis dans ``fold_in_compressibility_curve``.
    """
    values = np.asarray(values, dtype=float)
    half = int(half)
    if half < 1:
        return values
    if values.size < 2 * half + 1:
        return values.copy()
    kernel = np.ones(2 * half + 1) / (2 * half + 1)
    return np.convolve(values, kernel, mode="valid")


def compressibility_gain_curve(
    states: Sequence,
    window: int,
    horizon: int,
    smooth: int = 3,
    level: int = 9,
) -> Tuple[np.ndarray, np.ndarray]:
    """Gain de compressibilité sur un horizon (la courbe porteuse de « beauté »).

    Lisse ``local_compressibility`` puis calcule
    ``delta[t] = smoothedK[t-horizon] - smoothedK[t]`` : positif quand la fenêtre
    récente se compresse **mieux** que la fenêtre de reference (il y a ``horizon``
    pas plus tot) -- signature d'une découverte / compression-progress de
    Schmidhuber.

    Renvoie ``(steps_valid, delta)`` alignes sur la partie valide (apres
    lissage + horizon). ``delta`` vaut ``nan`` avant ``horizon``.
    """
    steps, K = local_compressibility(states, window=window, level=level)
    Ks = smooth_curve(K, smooth)
    delta = np.full(Ks.shape, np.nan)
    if Ks.size > horizon:
        delta[horizon:] = Ks[:-horizon] - Ks[horizon:]
    steps_s = steps[: Ks.size]
    return steps_s, delta


# --------------------------------------------------------------------------- #
#  Evenements de beaute (gate operationnel)                                   #
# --------------------------------------------------------------------------- #


def _matched_iid_control_max(
    states: Sequence,
    window: int,
    horizon: int,
    smooth: int,
    level: int,
    n_control: int,
    rng: np.random.Generator,
) -> np.ndarray:
    """Distribution nulle des max de gain, sous iid apparié (même n, même alphabet).

    Pour chaque contrôle iid, on recalcule la courbe de gain et on prend son
    max (le biais du max est positif -> c'est lui qu'on doit seuiller). Renvoie
    le tableau des ``n_control`` maxima.
    """
    n_symbols = max(canonical_int_sequence(states)) + 1 if len(states) else 0
    n = len(states)
    out: List[float] = []
    for _ in range(int(n_control)):
        iid = list(rng.integers(0, n_symbols, size=n))
        _, d = compressibility_gain_curve(iid, window=window, horizon=horizon,
                                          smooth=smooth, level=level)
        finite = d[np.isfinite(d)]
        if finite.size:
            out.append(float(finite.max()))
    return np.asarray(out, dtype=float)


def beauty_events(
    states: Sequence,
    window: int = 60,
    horizon: int = 40,
    smooth: int = 3,
    level: int = 9,
    k: float = 2.5,
    n_control: int = 50,
    rng: Optional[np.random.Generator] = None,
) -> dict:
    """Detecte les sauts de compressibilite (evenements de beauté de Schmidhuber).

    Un evenement est un **maximum local** de la courbe de gain
    (``compressibility_gain_curve``) qui depasse ``mean(ctrl_max) + k*std``
    ou le contrôle est un iid apparié (même longueur, même alphabet). On
    peak-pick les maxima locaux : une découverte unique = un evenement au pic,
    pas toute la rampe ascendante.

    Parametres
    ----------
    states : sequence
        Trajectoire d'etats (labels quelconques, canonises).
    window : int
        Fenêtre glissante pour ``local_compressibility``. Doit etre assez large
        (>= ~40 pour un alphabet de 4 symboles) pour dominer la variance de
        quantification zlib (defaut 60).
    horizon : int
        Pas d'integration du gain (defaut 40). Trop court = bruit ; trop long =
        moyenne trop lisse.
    smooth : int
        Demi-largeur de lissage (defaut 3).
    level : int
        Niveau zlib (defaut 9, reproductibilite).
    k : float
        Seuil en ecarts-types au-dessus du max-null moyen (defaut 2.5).
    n_control : int
        Nombre de controles iid (defaut 50). Cout ~ ``n_control * n`` appels
        zlib sur des fenêtres de ``window`` octets.
    rng : numpy Generator, optionnel (defaut graine 0).

    Retourne
    --------
    dict :
        * ``events`` : liste de ``(step, gain)`` (maxima locaux au-dessus du seuil),
        * ``steps``, ``gain`` : la courbe de gain (tableaux, ``nan`` avant ``horizon``),
        * ``control_mean``, ``control_std`` : stats du null (max iid),
        * ``threshold`` : ``control_mean + k * control_std`` (float),
        * ``n_control``, ``k`` : parametres records,
        * ``n_events`` : ``len(events)``,
        * ``verdict`` : ``"beauty"`` si ``n_events > 0`` sinon ``"flat"``.
    """
    rng = rng or np.random.default_rng(0)
    steps, gain = compressibility_gain_curve(
        states, window=window, horizon=horizon, smooth=smooth, level=level
    )
    ctrl = _matched_iid_control_max(
        states, window=window, horizon=horizon, smooth=smooth,
        level=level, n_control=n_control, rng=rng,
    )
    control_mean = float(ctrl.mean()) if ctrl.size else 0.0
    control_std = float(ctrl.std()) if ctrl.size else 0.0
    threshold = control_mean + float(k) * control_std

    # Peak-picking : maxima locaux de `gain` (>= voisins) au-dessus du seuil.
    events: List[Tuple[float, float]] = []
    g = gain
    for i in range(1, g.size - 1):
        v = g[i]
        if not np.isfinite(v):
            continue
        if v > threshold and v >= g[i - 1] and v > g[i + 1]:
            events.append((float(steps[i]), float(v)))

    return {
        "events": events,
        "steps": steps,
        "gain": gain,
        "control_mean": control_mean,
        "control_std": control_std,
        "threshold": threshold,
        "n_control": int(n_control),
        "k": float(k),
        "n_events": len(events),
        "verdict": "beauty" if events else "flat",
    }


# --------------------------------------------------------------------------- #
#  Diagnostic de pli (overlay Thom, exploratoire)                              #
# --------------------------------------------------------------------------- #


def fold_in_compressibility_curve(
    steps: np.ndarray,
    local_K: np.ndarray,
    smooth: int = 3,
) -> dict:
    """Cherche la geometrie d'un pli (fronce de Thom) dans la courbe local_K.

    Traite ``local_K`` comme un signal 1D sur ``steps``. Un **pli** est un point
    ou la derivee premiere presente un extremum local marque ET la courbure est
    maximale : la compressibilité *bascule* entre deux regimes (bassin
    incompressible <-> bassin compressible) plutot que de glisser douce­ment.
    C'est l'analogue 1D discret du pli de ``catastrophe.fold_lines``.

    **Exploratoire** : ce diagnostic ne prouve pas une vraie fronce (il
    faudrait un ajustement de cusp parametrique). Il fournit un *candidat* de
    pli -- le pas de courbure maximale -- a confronter aux evenements de beaute
    dans le notebook ICT-26.

    Retourne ``dict(fold_step | None, fold_curvature, curvature, smooth)``.
    """
    s = np.asarray(steps, dtype=float)
    r = np.asarray(local_K, dtype=float)
    sm = int(smooth)
    if r.size < 2 * sm + 5:
        return {"fold_step": None, "fold_curvature": 0.0,
                "curvature": np.array([], dtype=float), "smooth": sm}

    # Lissage valide puis derivee premiere et seconde discretes.
    r_s = smooth_curve(r, sm)
    s_s = s[: r_s.size]
    d1 = np.gradient(r_s)
    d2 = np.gradient(d1)
    curvature = d2

    finite = np.isfinite(curvature)
    if not np.any(finite):
        return {"fold_step": None, "fold_curvature": 0.0,
                "curvature": curvature, "smooth": sm}

    # Candidat : max absolu de la courbure, en un pas ou la pente est petite
    # (la derivee premiere s'annule au passage de bassin). On restreint aux
    # pas ou |d1| <= mediane(|d1|) pour eviter les monotonies pures.
    d1_scale = np.median(np.abs(d1[np.isfinite(d1)])) if np.any(np.isfinite(d1)) else 0.0
    mask = np.abs(d1) <= (d1_scale + 1e-12)
    if not np.any(mask):
        mask = np.ones_like(curvature, dtype=bool)
    cand = np.where(mask, np.abs(curvature), -np.inf)
    j = int(np.argmax(cand))
    if not np.isfinite(cand[j]):
        return {"fold_step": None, "fold_curvature": 0.0,
                "curvature": curvature, "smooth": sm}

    return {
        "fold_step": float(s_s[j]),
        "fold_curvature": float(curvature[j]),
        "curvature": curvature,
        "smooth": sm,
    }


def diagnose(
    states: Sequence, window: int = 60, horizon: int = 40,
    smooth: int = 3, level: int = 9, **kw
) -> dict:
    """Couple le gate operationnel et le diagnostic de pli.

    Renvoie le dict de ``beauty_events`` augmente de ``fold`` (le dict de
    ``fold_in_compressibility_curve`` calcule sur la meme courbe ``local_K``
    lissee). Une découverte co-localisee avec un candidat pli est la signature
    Thom<->Schmidhuber que ce module cherche a mettre en evidence ; le notebook
    ICT-26 quantifiera la co-localisation sur des trajectoires de reference.
    """
    rep = beauty_events(states, window=window, horizon=horizon, smooth=smooth,
                        level=level, **kw)
    steps_k, K = local_compressibility(states, window=window, level=level)
    rep["fold"] = fold_in_compressibility_curve(steps_k, K, smooth=smooth)
    return rep


# =========================================================================== #
#  COUCHE 2 -- Frontiere MDL : Levin / PowerPlay / Speed Prior                 #
#  (formalisation du compression-progress de Schmidhuber, See #7258)           #
# =========================================================================== #
#
# La couche 1 operationnalise la beaute de Schmidhuber (saut de compressibilite
# = compression-progress) de facun EMPIRIQUE : zlib sur une fenetre glissante,
# controle iid apparie. La couche 2 en donne la formalisation MDL : la
# *frontiere* de description d'une trajectoire a mesure qu'elle s'etend, et sa
# derivee (compression-progress en code en deux parties). Elle ajoute aussi les
# deux machineries de Schmidhuber qui cadrent cette frontiere :
#
#   - la **complexite de Levin** ``Kt = program_bits + log2(runtime)`` et la
#     **Speed Prior** ``2^{-Kt}`` (Schmidhuber 2000) : un programme court mais
#     lent coute plus a *trouver* qu'un programme legerement plus long mais
#     rapide -- le cout universel de la recherche ;
#   - la frontiere **PowerPlay** (Schmidhuber 2011) : l'agent ne garde une
#     nouvelle theorie que si elle resout toutes les taches precedentes **et**
#     au moins une nouvelle -- compression-progress monotone, sans abandon.
#
# La derivee de la frontiere PowerPlay EST le compression-progress : la beaute
# de la couche 1, formalisee en MDL plutot qu'estimee par zlib.
#
# Caveat honnete (cf comments de l'issue #7258) : appliquee a la *string de
# predictions* d'un reseau en phase de grokking, la frontiere MDL localise la
# MEMORISATION, pas le grok -- la MDL de la string recompense la structure
# Markovienne parcimonieuse qu'engendre la memorisation (table lookup). Sur une
# transition de structure veritable (bruit iid -> cycle deterministe), en
# revanche, le cycle est nettement moins couteux par symbole que le bruit
# (gate B4 du test). Le notebook strand confronte honnetement cette limite sur
# le grokking et explore la description length *des poids* (information de
# Fisher) comme proxy K-modele.
# =========================================================================== #


def levin_complexity(program_bits: float, runtime_steps: float) -> float:
    """Complexite de Levin ``Kt = program_bits + log2(runtime_steps)``.

    Cout universel de *trouver* un programme par recherche de Levin (Levin
    1973) : on somme la longueur du programme (simplicite) et le logarithme
    du nombre de pas d'execution (rapidite). Un programme court mais lent
    coute plus a decouvrir qu'un programme legerement plus long mais rapide.
    C'est la fonction de cout sous-jacente a la **Speed Prior** de Schmidhuber
    (2000), qui pondere chaque programme par ``2^{-Kt}`` (cf
    ``speed_prior_weight``).

    Parametres :
      - ``program_bits`` : longueur de description du programme (>= 0).
      - ``runtime_steps`` : nombre de pas d'execution (>= 1).

    Retourne ``Kt`` en bits (log base 2).
    """
    if program_bits < 0:
        raise ValueError(f"program_bits doit etre >= 0, recu {program_bits}")
    if runtime_steps < 1:
        raise ValueError(
            f"runtime_steps doit etre >= 1, recu {runtime_steps}"
        )
    return float(program_bits) + math.log2(float(runtime_steps))


def speed_prior_weight(program_bits: float, runtime_steps: float) -> float:
    """Poids **Speed Prior** de Schmidhuber : ``2^{-Kt}`` avec ``Kt`` de Levin.

    Probabilite a priori qu'un programme tire selon la Speed Prior soit ce
    programme-ci : decroit exponentiellement avec la complexite de Levin
    (longueur + log temps). Les programmes courts et rapides dominent. Cette
    ponderation est le prior naturel sous lequel l'agent cherche le prochain
    saut de compression (la frontiere PowerPlay).
    """
    return 2.0 ** (-levin_complexity(program_bits, runtime_steps))


def powerplay_frontier(theories: Sequence) -> dict:
    """Frontiere **PowerPlay** de Schmidhuber (2011) : compression-progress monotone.

    PowerPlay est un agent qui ne garde une nouvelle theorie que si elle resout
    **toutes** les taches deja resolues par la theorie courante **et** au moins
    une tache nouvelle -- le progres de compression est monotone (aucune tache
    abandonee). La *frontiere* est la suite des theories acceptees : elle
    avance dans le plan (longueur de programme ``K``, nombre cumul de taches
    resolues), et sa derivee **est** le compression-progress (la beaute de la
    couche 1, ici formalisee en MDL plutot qu'estimee par zlib).

    Version stricte (sans abandon de tache) : un candidat qui lache une tache
    deja resolue est rejete, mene s'il en resout de nouvelles. L'extension
    PowerPlay generale (abandon tolerate si le net de compression est positif)
    est laisse au notebook.

    Parametres :
      - ``theories`` : sequence de couples ``(program_bits, solved)`` ou
        ``solved`` est un ensemble (ou iterable) de labels de taches resolues,
        dans l'ordre ou l'agent les rencontre.

    Retourne ``{"frontier": [...], "rejected": [...], "total_accepted": int}``
    ou chaque entree acceptee contient ``index, program_bits,
    cumulative_solved, new`` et chaque rejet ``index, program_bits, reason``
    (``"no_new"`` = aucune tache nouvelle ; ``"dropped_existing"`` = une tache
    deja resolue est perdue).
    """
    accepted: List[dict] = []
    rejected: List[dict] = []
    cumulative: frozenset = frozenset()
    for idx, entry in enumerate(theories):
        kbits, solved = entry
        solved_fs = frozenset(solved)
        grows = len(solved_fs) > len(cumulative)
        keeps_all = cumulative <= solved_fs
        if grows and keeps_all:
            accepted.append({
                "index": int(idx),
                "program_bits": float(kbits),
                "cumulative_solved": len(solved_fs),
                "new": len(solved_fs) - len(cumulative),
            })
            cumulative = solved_fs
        else:
            reason = "dropped_existing" if not keeps_all else "no_new"
            rejected.append({
                "index": int(idx),
                "program_bits": float(kbits),
                "reason": reason,
            })
    return {"frontier": accepted, "rejected": rejected,
            "total_accepted": len(accepted)}


def mdl_frontier(states: Sequence,
                 prefix_schedule: Optional[Sequence[int]] = None,
                 split: float = 0.5, n_points: int = 10) -> dict:
    """Courbe MDL (``two_part_code``) sur des prefixes croissants de la trajectoire.

    Pour chaque longueur de prefix ``L``, estime le code en deux parties
    (``ict.mdl.two_part_code``) sur ``states[:L]`` : ``model_bits`` (TPM sous
    prior KT) + ``residual_bits`` (-log2 proba held-out) = ``total_bits``.
    C'est l'analogue MDL-formel de ``local_compressibility`` (couche 1 zlib) :
    la frontiere de description de la trajectoire a mesure qu'elle s'etend. Sa
    derivee (``mdl_compression_progress``) = compression-progress en termes de
    code en deux parties.

    **Caveat honnete (cf comments #7258)** : appliquee a la *string de
    predictions* d'un reseau en phase de grokking, cette frontiere localise la
    memorisation, pas le grok -- la MDL de la string recompense la structure
    Markovienne parcimonieuse qu'engendre la memorisation. Sur une transition
    de structure veritable (bruit iid -> cycle deterministe), en revanche, le
    cycle est nettement moins couteux par symbole que le bruit (gate B4 du
    test) : la machinerie est correcte, c'est son application naive au grokking
    qui est piegeuse.

    Parametres :
      - ``states`` : trajectoire d'etats.
      - ``prefix_schedule`` : longueurs de prefix a evaluer (defaut :
        ``n_points`` points echantillonnes entre ~10% et 100% de la
        trajectoire).
      - ``split`` : proportion train/held-out pour ``two_part_code``
        (defaut 0.5).
      - ``n_points`` : nombre de points si ``prefix_schedule`` est None.

    Retourne ``{"rows": [...]}`` ou chaque row contient ``L, model_bits,
    residual_bits, total_bits, bits_per_symbol``.
    """
    from . import mdl as MDL

    seq = list(states)
    n = len(seq)
    if n < 2:
        raise ValueError(f"il faut au moins 2 etats, recu n={n}")
    if prefix_schedule is None:
        lo = max(2, int(round(0.1 * n)))
        if n <= lo:
            prefix_schedule = [n]
        else:
            grid = {int(round(lo + (n - lo) * i / max(n_points - 1, 1)))
                    for i in range(n_points)}
            prefix_schedule = sorted(p for p in grid if 2 <= p <= n)
    rows: List[dict] = []
    for L in prefix_schedule:
        L = int(L)
        if L < 2 or L > n:
            continue
        try:
            r = MDL.two_part_code(seq[:L], split=split)
        except ValueError:
            continue
        total = float(r["total_bits"])
        rows.append({
            "L": L,
            "model_bits": float(r["model_bits"]),
            "residual_bits": float(r["residual_bits"]),
            "total_bits": total,
            "bits_per_symbol": total / L,
        })
    return {"rows": rows}


def mdl_compression_progress(states: Sequence,
                             prefix_schedule: Optional[Sequence[int]] = None,
                             split: float = 0.5, n_points: int = 10,
                             horizon: int = 2) -> dict:
    """Derivee de la frontiere MDL = compression-progress formel.

    Calcule ``mdl_frontier`` puis, sur ``bits_per_symbol``,
    ``delta[i] = bps[i-horizon] - bps[i]`` : positif quand le prefix recent se
    decrit plus economiquement (progress de compression), negatif s'il devient
    plus couteux. C'est l'analogue MDL de ``compressibility_gain_curve``
    (couche 1) : la courbe porteuse de beaute, en code en deux parties plutot
    qu'en zlib.

    Pas de controle iid ici (contrairement a ``beauty_events``) : la frontiere
    MDL est Deterministe sur une trajectoire fixee, et la quantification MDL
    (TPM KT) est beaucoup moins bruitee que zlib -- on present le signal brut
    a l'utilisateur du module ; le seuil/event-picking est laisse au notebook,
    ou il se confronte au caveat grokking (comments #7258).

    Retourne ``{"rows": [...], "max_progress": float, "argmax_L": int|None}``
    ou chaque row contient ``L, bits_per_symbol, delta`` (``delta`` = ``nan``
    pour les ``horizon`` premiers points).
    """
    front = mdl_frontier(states, prefix_schedule=prefix_schedule, split=split,
                         n_points=n_points)
    rows = front["rows"]
    h = int(horizon)
    if h < 1:
        raise ValueError(f"horizon doit etre >= 1, recu {h}")
    out: List[dict] = []
    for i, r in enumerate(rows):
        d = float("nan")
        if i >= h:
            d = float(rows[i - h]["bits_per_symbol"] - r["bits_per_symbol"])
        out.append({
            "L": r["L"],
            "bits_per_symbol": r["bits_per_symbol"],
            "delta": d,
        })
    finite = [(r["delta"], r["L"]) for r in out if np.isfinite(r["delta"])]
    if finite:
        max_d, arg_L = max(finite, key=lambda t: t[0])
    else:
        max_d, arg_L = float("nan"), None
    return {"rows": out, "max_progress": float(max_d), "argmax_L": arg_L}
