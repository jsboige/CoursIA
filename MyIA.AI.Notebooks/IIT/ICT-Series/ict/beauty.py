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

from . import mdl as MDL
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


def _events_from_gain(
    steps: np.ndarray, gain: np.ndarray, threshold: float
) -> List[Tuple[float, float]]:
    """Peak-picking partage : maxima locaux de ``gain`` au-dessus du seuil.

    Un evenement = un pas ou ``gain[i]`` est un maximum local
    (``>= g[i-1]`` ET ``> g[i+1]``) strictement au-dessus du seuil. Les valeurs
    non finies (``nan`` avant l'horizon) sont ignorees. Utilise par
    ``beauty_events`` (zlib) et ``powerplay_events`` (MDL) -- la *methode* de
    detection (peak-picking au-dessus d'un seuil iid) est commune, seul
    l'estimateur de K change.
    """
    s = np.asarray(steps, dtype=float)
    g = np.asarray(gain, dtype=float)
    out: List[Tuple[float, float]] = []
    for i in range(1, g.size - 1):
        v = g[i]
        if not np.isfinite(v):
            continue
        if v > threshold and v >= g[i - 1] and v > g[i + 1]:
            out.append((float(s[i]), float(v)))
    return out


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
    events = _events_from_gain(steps, gain, threshold)

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


# --------------------------------------------------------------------------- #
#  Couche 2 -- Levin / Speed Prior / PowerPlay (estimateur MDL explicite)      #
# --------------------------------------------------------------------------- #
#  La couche 1 mesure K via zlib -- un estimateur BRUT, sans modele (le docstring
#  de la couche 1 le dit honnetement). Cette couche remplace zlib par le **code
#  MDL en deux parties** de ``mdl.two_part_code`` (modele Markov KT + residu
#  held-out) -- l'operationnalisation *principiee* de K. Elle ajoute ensuite la
#  pondération de **Levin / speed prior** (Kt = |programme| + log2(temps)) et le
#  detecteur **PowerPlay** (Schmidhuber 2011 : frontiere du « compressible-mais-
#  pas-encore-compresse »), en reutilisant la meme methodologie qu'en couche 1
#  (fenetre glissante, controle iid apparie, seuil mean+k*std sur le max-null).
#
#  Honnetete : « programme » = le modele Markov appris, « temps » = le nombre
#  d'echantillons pour l'identifier. Ce n'est PAS la machine de Turing universelle
#  de Solomonoff/Levin (incomputable) -- c'est son proxy MDL fini, documente comme
#  tel. Le notebook strand (ICT-grokking) confrontera les deux estimateurs
#  (zlib couche 1 vs MDL couche 2) sur la trajectoire de grokking.
# --------------------------------------------------------------------------- #


def mdl_compressibility_curve(
    states: Sequence, window: int, split: float = 0.5
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Compressibilite locale par code MDL deux parties (couche 2).

    Analogue MDL-explicite de ``local_compressibility`` (couche 1, zlib) : pour
    chaque fenetre pleine ``states[t-window:t]`` on estime une TPM sous prior KT
    et on evalue le code en deux parties ``model_bits + residual_bits``. Une
    fenetre structuree (cycle, regle) -> residu faible -> ``total_bits`` bas ;
    une fenetre aleatoire -> residu eleve -> ``total_bits`` haut. C'est le
    signal K *principe* dont on tire la derivee « beaute ».

    Parametres
    ----------
    states : sequence d'etats (labels canonises par ``two_part_code``).
    window : largeur de la fenetre glissante. Doit etre >= 4 (estimer une TPM
        k x k significative sur un alphabet de 4 symboles demande suffisamment
        de transitions).
    split : proportion de transitions d'apprentissage pour ``two_part_code``
        (defaut 0.5). Voir ``mdl.two_part_code``.

    Retourne ``(steps, total_bits, model_bits, residual_bits)`` sur les fenetres
    pleines (alignes).

    Honnetete : ``total_bits`` peut etre **negatif** pour une fenetre tres
    structuree (cycle deterministe). C'est une propriete de l'estimateur KT de
    ``mdl.two_part_code`` : le terme ``-k*log2(k+0.5)`` credite les TPM
    parcimonieuses, donc une matrice de permutation (cycle) donne un
    ``model_bits`` tres negatif et un residu ~0. La **signe** n'a pas de sens
    absolu ici ; seules les **differences** (gain sur horizon) portent le signal
    « decouverte » utilise par ``powerplay_events``. Estimateur plus bruite que
    zlib sur courtes fenetres (variance d'estimation de la TPM) : preferer
    ``window >= ~60`` pour stabiliser le controle iid (verifie empiriquement).
    """
    if window < 4:
        raise ValueError(
            f"window doit etre >= 4 pour estimer une TPM, recu {window}"
        )
    seq = list(states)
    n_windows = max(len(seq) - window + 1, 0)
    steps = np.arange(window, len(seq) + 1, dtype=float)
    total = np.zeros(n_windows, dtype=float)
    model = np.zeros(n_windows, dtype=float)
    resid = np.zeros(n_windows, dtype=float)
    for idx, t in enumerate(range(window, len(seq) + 1)):
        rep = MDL.two_part_code(seq[t - window:t], split=split)
        total[idx] = rep["total_bits"]
        model[idx] = rep["model_bits"]
        resid[idx] = rep["residual_bits"]
    return steps, total, model, resid


def levin_speed_prior_curve(
    states: Sequence,
    window: int,
    split: float = 0.5,
    speed_weight: float = 1.0,
) -> Tuple[np.ndarray, np.ndarray]:
    """Courbe de complexite de Levin Kt = |programme| + log2(temps) (couche 2).

    Operationnalisation finie du speed prior de Levin (1973) / Schmidhuber (2002)
    pour une trajectoire discrete :

    * le « **programme** » = le modele Markov appris, dont la longueur est
      ``model_bits`` (KT-codelength de la TPM) ;
    * le « **temps** » = le nombre d'echantillons necessaires pour identifier ce
      modele = ``n_train = floor(split * (window-1))`` (proportionnel a la
      fenetre d'apprentissage).

    Un modele court qu'on ne peut identifier qu'avec une masse de donnees est
    penalise -- c'est le trade-off central de Levin : la simplicite du programme
    ne suffit pas, il faut aussi qu'il soit *trouvable* vite. C'est exactement
    la distinction que la couche 1 (zlib) ne pouvait pas exprimer.

    ``levin_bits[t] = total_bits[t] + speed_weight * log2(n_train)``.

    Parametres
    ----------
    speed_weight : poids du terme de Levin (defaut 1.0). ``0.0`` retombe sur
        ``total_bits`` (K Solomonoff pur, sans penalty de vitesse).

    Retourne ``(steps, levin_bits)``.
    """
    steps, total, _, _ = mdl_compressibility_curve(states, window, split=split)
    n_train = max(int(math.floor(split * (window - 1))), 1)
    levin = total + float(speed_weight) * math.log2(max(n_train, 2))
    return steps, levin


def _mdl_gain_and_control(
    states: Sequence,
    window: int,
    horizon: int,
    split: float,
    speed_weight: float,
    smooth: int,
    n_control: int,
    rng: np.random.Generator,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Courbe de gain MDL (delta levin sur horizon) + distribution nulle iid.

    Même structure qu'en couche 1 : lissage valide de la courbe de Levin, puis
    ``delta[t] = levin_s[t-horizon] - levin_s[t]`` (positif = la fenetre recente
    se code mieux -> decouverte). Le controle est un iid apparie (meme longueur,
    meme alphabet) dont on tire le max de gain (biais du max -> seuillage sur la
    moyenne du null).
    """
    steps, levin = levin_speed_prior_curve(
        states, window=window, split=split, speed_weight=speed_weight
    )
    levin_s = smooth_curve(levin, smooth) if smooth else levin
    steps_s = steps[: levin_s.size]
    delta = np.full(levin_s.shape, np.nan)
    if levin_s.size > horizon:
        delta[horizon:] = levin_s[:-horizon] - levin_s[horizon:]

    n_symbols = max(canonical_int_sequence(states)) + 1 if len(states) else 0
    n = len(states)
    ctrl_max: List[float] = []
    for _ in range(int(n_control)):
        iid = list(rng.integers(0, n_symbols, size=n))
        _, lk = levin_speed_prior_curve(
            iid, window=window, split=split, speed_weight=speed_weight
        )
        lk_s = smooth_curve(lk, smooth) if smooth else lk
        dk = np.full(lk_s.shape, np.nan)
        if lk_s.size > horizon:
            dk[horizon:] = lk_s[:-horizon] - lk_s[horizon:]
        finite = dk[np.isfinite(dk)]
        if finite.size:
            ctrl_max.append(float(finite.max()))
    return steps_s, delta, np.asarray(ctrl_max, dtype=float)


def powerplay_events(
    states: Sequence,
    window: int = 60,
    horizon: int = 40,
    split: float = 0.5,
    speed_weight: float = 1.0,
    smooth: int = 3,
    k: float = 2.5,
    n_control: int = 30,
    rng: Optional[np.random.Generator] = None,
) -> dict:
    """Decouvertes PowerPlay : pics du gain MDL (Levin) au-dessus du seuil iid.

    Schmidhuber **PowerPlay** (2011) : un agent continually expand la frontiere
    du « compressible-mais-pas-encore-compresse » -- il resout des problemes qu'il
    ne savait pas resoudre avant. Operationnalise ici comme les **pics** de la
    courbe de gain de code MDL (``levin_speed_prior_curve``) au-dessus du seuil
    iid apparie ``mean + k*std`` : une decouverte = un pic ou le code MDL chute
    brutalement sur un horizon. C'est le **detecteur de beaute MDL-explicite**,
    dual de ``beauty_events`` (zlib) -- même methodologie, estimateur de K
    different. Le notebook strand (ICT-grokking) confrontera les deux sur le
    grok point : on s'attend a co-localisation du pic zlib + du pic MDL + du pli.

    Parametres : voir ``beauty_events`` (window, horizon, smooth, k, n_control,
    rng) + ``split`` (proportion apprentissage MDL) et ``speed_weight`` (ponderation
    Levin ; 0.0 = Solomonoff pur). Le cout est ~ ``(n_control+1) * n_windows``
    appels a ``two_part_code`` -- garder ``n_control`` modeste (defaut 30).

    Retourne le meme dict que ``beauty_events`` augmente de ``method="mdl"`` et
    ``speed_weight`` ; ``verdict`` vaut ``"powerplay"`` si >=1 evenement sinon
    ``"flat"``.
    """
    rng = rng or np.random.default_rng(0)
    steps, delta, ctrl = _mdl_gain_and_control(
        states, window=window, horizon=horizon, split=split,
        speed_weight=speed_weight, smooth=smooth,
        n_control=n_control, rng=rng,
    )
    control_mean = float(ctrl.mean()) if ctrl.size else 0.0
    control_std = float(ctrl.std()) if ctrl.size else 0.0
    threshold = control_mean + float(k) * control_std
    events = _events_from_gain(steps, delta, threshold)
    return {
        "events": events,
        "steps": steps,
        "gain": delta,
        "control_mean": control_mean,
        "control_std": control_std,
        "threshold": threshold,
        "n_control": int(n_control),
        "k": float(k),
        "n_events": len(events),
        "verdict": "powerplay" if events else "flat",
        "method": "mdl",
        "speed_weight": float(speed_weight),
    }
