"""Axe *Global Workspace* (GWT) de la serie ICT — adaptateur numpy-only (ICT-24).

Outille le notebook **ICT-24 — WorkspaceIgnition** (Epic #4588, strate 5). La
serie a construit une batterie de **complexite integree** au sens IIT (lecture
``ec_gain`` / ``fe_gain`` / ``k_gain`` creditee au-dessus d'un controle shuffle
dans :mod:`ict.synthesis`, cf. capstone ICT-15 / #5090 / #5102). L'article
Anthropic (*Global Workspace in Claude*, 2025) identifie dans un grand modele
un **workspace global** — la lecture GWT (Baars ; Dehaene, Naccache, Changeux),
theorie historiquement *contrastee* avec l'IIT. Les deux lectures n'ont presque
jamais ete confrontees **sur le meme substrat avec le meme appareil**. Les
traces SAE du pipeline #5101 (substrat S4) rendent la confrontation possible.

Question fondatrice, en **hypothese falsifiable** : *sur S4, les evenements
d'acces global co-localisent-ils avec les pics de complexite integree creditee ?*
OUI -> pont empirique (un meme evenement, deux lectures theoriques). NON ->
dissociation mesuree, negative honnete tout aussi precieuse. Les Gates 22-23
(livraison GPU-free, outilles ici) tranchent l'observation ; le Gate 24
(ablation selective, GPU, phase 2 / #5635) tranche seul la causalite.

Pourquoi un adaptateur, pas une reinvention
--------------------------------------------
La batterie d'emergence causale (TPM etat-a-etat, controle shuffle, gain
credite) vit deja dans :mod:`ict.synthesis` et :mod:`ict.causal_emergence` ;
elle a ete appliquee a l'identique a trois substrats (tri, Gray-Scott,
replicateur) dans le capstone ICT-15. Ce module est volontairement un
**adaptateur mince** (precedent : :mod:`ict.feature_dynamics`) qui ajoute
quatre primitives **specifiques au cas d'usage GWT** :

* :func:`concentration_series` -- **participation ratio / Gini par pas** sur le
  panel d'activations elargi. Mesure a chaque pas temporel a quel point
  l'activite est concentree sur un petit sous-ensemble de features. C'est le
  signal brut dont on tirera les ignitions (lecture Dehaene temporelle, NOTRE
  contribution -- l'article Anthropic mesure le cablage, PAS l'ignition).
* :func:`ignition_events` -- detecteur de **pics de concentration persistants**
  (seuil + duree documentes). Analogue temporel de l'allumage brutal du
  reseau fronto-parietal decrit par Dehaene en IRM/EEG.
* :func:`lagged_influence` + :func:`fanout_profile` + :func:`workspace_candidates`
  -- chaine observationnelle **Gate 22** : matrice d'influence laggee entre
  features, profil de fan-out par feature, selection du sous-ensemble a fan-out
  disproportionne (analogue observationnel du cablage ~100x d'Anthropic).
* :func:`event_triggered_battery` -- **Gate 23** : contraste event-triggered de
  la batterie d'emergence (reutilise :func:`ict.synthesis.emergence_gain`
  VERBATIM, meme rng, meme discipline de creditation) sur des fenetres centrees
  aux ignitions vs fenetres appariees hors-evenement.

Numpy uniquement (comme le reste du package leger ``ict``). Pas de torch, pas de
scipy, pas de transformers : le pipeline d'extraction des traces (SAE / jacobien
des logits) vit dans #5101 et reste confine au GPU ; le clamp du Gate 24 est un
hook de ce meme pipeline. Les traces reviennent en ``.npz`` et cet adaptateur
les consomme sans rien savoir de leur provenance.

Garde-fous d'honnetete (5) — a reporter dans le notebook
--------------------------------------------------------
1. **J-lens != SAE** -- l'article identifie le J-space par *jacobien des logits*,
   pas par SAE. Nous operationalisons parallelement (features SAE), nous ne
   repliquons pas. Ne pas vend re comme jacobien ce qui est activite SAE.
2. **structurel vs temporel** -- Anthropic mesure la **connectivite**
   (cablage), PAS l'ignition temporelle. L'ignition (pics de concentration
   persistants) est NOTRE lecture Dehaene, dite comme telle.
3. **observationnel != interventionnel** -- :func:`lagged_influence` est un
   PROXY observationnel (correlation laggee). Seul le Gate 24 (clamp sur le
   pipeline GPU) est causal. Ne pas ecrire "cause" la ou on mesure "correlation".
4. **Qwen != Claude** -- le substrat S4 est Qwen (poids ouverts, force
   pedagogique : reproductible), pas Claude. Ne pas importer les chiffres
   d'Anthropic (<10 % d'activite, ~100x de cablage) comme attendus : mesurer
   les notres, et les reporter tels quels.
5. **access != phenomenal** -- on bridge le **recouvrement fonctionnel /
   mechaniste** entre GWT et IIT sur ce substrat, pas la metaphysique de
   :math:`\\Phi`. Le claim est limite a l'access-consciousness.

References
----------
* Baars B., *A Cognitive Theory of Consciousness* (1988) -- la theorie du
  workspace global originelle.
* Dehaene S., Naccache L., *Towards a cognitive neuroscience of consciousness*
  (Nature Rev. Neurosci., 2001) ; Dehaene, Changeux -- l'ignition temporelle
  (P3b) que nos ``ignition_events`` operationalisent.
* Hoel E., *When the map is better than the territory* (Entropy, 2017) -- le
  cadre de l'emergence causale creditee au-dessus d'un controle shuffle, que
  :func:`event_triggered_battery` reutilise via :mod:`ict.synthesis`.
* Anthropic, *Global Workspace in Claude* (anthropic.com/research/global-workspace,
  2025) -- le substrat motivationnel ; J-space par jacobien, broadcast
  structurel, ablation selective comme preuve maitresse. IIT/Tononi absents.
"""

from __future__ import annotations

from typing import Dict, List, Sequence, Tuple

import numpy as np

from . import synthesis as SYN


# --------------------------------------------------------------------------- #
# Concentration du panel par pas temporel (Gate 23, signal brut de l'ignition)
# --------------------------------------------------------------------------- #
def concentration_series(acts: np.ndarray, metric: str = "gini") -> np.ndarray:
    """Concentration de l'activite par pas temporel (Gate 23, signal brut).

    Pour chaque pas ``t`` on mesure a quel point l'activite du panel
    ``acts[t]`` (K features) est **concentree** sur un petit sous-ensemble.
    Un pas "concentre" = peu de features portent la quasi-totalite de
    l'activite ; un pas "diffus" = toutes les features contribuent egalement.
    C'est le signal brut dont :func:`ignition_events` tire les pics.

    Parametres
    ----------
    acts : array (T, K)
        Activations non-negatives du panel elargi (K ~ 64). T = nombre de pas
        temporels. Le signe est pris en valeur absolue (une activation negative
        est une activation) puis normalise en proportions par pas.
    metric : {"gini", "participation_ratio"}
        * ``"gini"`` (defaut) -- coefficient de Gini sur les activations du pas,
          dans ``[0, 1]`` : 0 = parfaitement diffus (uniforme), 1 = parfaitement
          concentre (une seule feature porte tout). Intuitif pour l'ignition.
        * ``"participation_ratio"`` -- PR = ``(sum a_i)^2 / sum a_i^2`` dans
          ``[1, K]`` : 1 = concentre, K = uniforme. On renvoie ``1 - PR/K``
          ramene dans ``[0, 1]`` (1 = concentre) pour garder le meme sens que
          Gini. PR est la mesure utilisee en neuroscience pour la "concentration
          de variance" (un PR faible = peu de composantes portent la variance).

    Retour
    ------
    array (T,)
        Concentration par pas. Convention : un pas inactif (``sum a_i == 0``)
        renvoie 0 (rien de concentre, par convention -- a documenter dans le
        notebook). La serie est le substrat de :func:`ignition_events`.
    """
    a = np.abs(np.asarray(acts, dtype=float))
    if a.ndim != 2:
        raise ValueError(f"acts doit etre 2-D (T, K), got shape {a.shape}")
    T, K = a.shape
    rowsum = a.sum(axis=1)
    out = np.zeros(T, dtype=float)
    active = rowsum > 0
    a_act = a[active]
    p = a_act / a_act.sum(axis=1, keepdims=True)  # proportions par pas actif

    if metric == "gini":
        # Gini vectorise via tri CROISSANT (formule exacte, cf Wikipedia) :
        # G = 2 * sum(i * x_(i)) / (K * sum x) - (K+1)/K,  i = 1..K, x_(i) tries
        # croissants. Donne 0 pour uniforme, (K-1)/K pour [0,..,0,1]. On normalise
        # par le max theorique (K-1)/K -> [0, 1]. Ici sum x = 1 (p normalise).
        order = np.argsort(p, axis=1)  # croissant
        p_sorted = np.take_along_axis(p, order, axis=1)
        weights = np.arange(1, K + 1, dtype=float)
        gini = 2.0 * (p_sorted * weights).sum(axis=1) / K - (K + 1.0) / K
        gini_max = (K - 1.0) / K
        gini = np.clip(gini / gini_max if gini_max > 0 else gini, 0.0, 1.0)
        out[active] = gini
    elif metric == "participation_ratio":
        pr = (p.sum(axis=1) ** 2) / (p ** 2).sum(axis=1)  # dans [1, K]
        out[active] = 1.0 - pr / K  # 1 = concentre
    else:
        raise ValueError(f"metric inconnu: {metric!r} (attendu 'gini' ou 'participation_ratio')")
    return out


# --------------------------------------------------------------------------- #
# Detection d'ignitions (lecture Dehaene temporelle)
# --------------------------------------------------------------------------- #
def ignition_events(
    conc: np.ndarray,
    threshold: float,
    persistence: int = 3,
) -> List[Dict]:
    """Detecte les evenements d'**ignition** (pics de concentration persistants).

    Une ignition = fenetre contigue d'au moins ``persistence`` pas ou la
    concentration ``conc`` depasse ``threshold``. C'est NOTRE lecture
    **Dehaene temporelle** (garde-fou #2) : un allumage brutal et soutenu de
    l'activite sur un petit sous-ensemble de features. L'article Anthropic ne
    mesure PAS l'ignition temporelle -- seulement la connectivite structurelle.

    Parametres
    ----------
    conc : array (T,)
        Serie de concentration par pas (cf. :func:`concentration_series`).
    threshold : float
        Seuil de concentration au-dessus duquel un pas est "allume". A calibrer
        sur la distribution empirique de ``conc`` dans le notebook (ex:
        quantile 0.9) et **documente** comme tel -- un seuil arbitraire sans
        justification = lecture non reproductible.
    persistence : int
        Nombre **minimum** de pas consecutifs au-dessus du seuil pour qu'une
        ignition soit declaree. Filtre les pics isoles (bruit). ``persistence=1``
        = tout pic compte ; ``persistence >= 3`` recommande pour un analogique
        honnete du P3b (qui dure de la dizaine aux centaines de ms).

    Retour
    ------
    list[dict]
        Un dict par ignition : ``start`` / ``end`` (indices, demi-ouvert),
        ``center`` (indice du pic de concentration dans la fenetre), ``peak``
        (valeur de concentration au pic), ``length`` (duree en pas). Vide si
        aucune fenetre ne franchit le seuil assez longtemps.
    """
    c = np.asarray(conc, dtype=float).ravel()
    T = len(c)
    if T == 0 or persistence < 1:
        return []
    over = c >= threshold
    events: List[Dict] = []
    t = 0
    while t < T:
        if not over[t]:
            t += 1
            continue
        start = t
        while t < T and over[t]:
            t += 1
        end = t  # demi-ouvert
        if end - start >= persistence:
            seg = c[start:end]
            peak_idx_rel = int(np.argmax(seg))
            events.append({
                "start": int(start),
                "end": int(end),
                "center": int(start + peak_idx_rel),
                "peak": float(seg[peak_idx_rel]),
                "length": int(end - start),
            })
    return events


# --------------------------------------------------------------------------- #
# Influence laggee entre features (Gate 22, PROXY observationnel)
# --------------------------------------------------------------------------- #
def lagged_influence(
    acts: np.ndarray,
    max_lag: int = 5,
) -> Dict[str, np.ndarray]:
    """Matrice d'influence **laggee** entre features (Gate 22, PROXY).

    Pour chaque paire ``(i, j)`` de features et chaque retard ``tau`` dans
    ``[1, max_lag]``, on calcule la correlation de Pearson entre l'activite de
    ``i`` au temps ``t - tau`` et l'activite de ``j`` au temps ``t``. On agregere
    en retenant, pour chaque paire ``(i, j)``, le retard qui maximise la
    correlation en valeur absolue.

    **GARDE-FOU #3 (a reporter dans le notebook)** : c'est un **proxy
    observationnel**. Une correlation laggee elevee n'est PAS une relation
    causale -- deux features peuvent suivre une cause commune. Seul le Gate 24
    (clamp sur le pipeline GPU) est interventionnel. Ne pas ecrire "i cause j" ;
    ecrire "i precede et predit j au retard tau".

    C'est l'analogue observationnel du **cablage ~100x** d'Anthropic (garde-fou
    #2 et #4) -- mais Anthropic mesure la connectivite du **jacobien des logits**
    (structurelle), pas une lag-correlation sur les activite SAE. Mesurer les
    notres, ne pas importer leurs chiffres comme attendus.

    Parametres
    ----------
    acts : array (T, K)
        Activations du panel. Centrees et reduites par colonne en interne (la
        correlation est invariante par normalisation affine).
    max_lag : int
        Retard maximum teste, en pas temporels. ``max_lag >= 1``. Typiquement
        petit (3-8) : on cherche une influence directe a court terme, pas des
        boucles longues.

    Retour
    ------
    dict
        ``matrix`` : array (K, K), ``matrix[i, j]`` = correlation (signee) au
        meilleur retard de l'influence ``i -> j``. ``best_lag`` : array (K, K)
        int, le retard correspondant. ``max_lag`` : int (echo). La diagonale
        est forced a 0 (un feature ne s'influence pas lui-meme via ce canal).
    """
    a = np.asarray(acts, dtype=float)
    if a.ndim != 2:
        raise ValueError(f"acts doit etre 2-D (T, K), got shape {a.shape}")
    if max_lag < 1:
        raise ValueError(f"max_lag >= 1 requis, got {max_lag}")
    T, K = a.shape

    # centrer-reduire par colonne pour une correlation de Pearson coherente
    mu = a.mean(axis=0, keepdims=True)
    sd = a.std(axis=0, keepdims=True)
    sd[sd == 0] = 1.0
    z = (a - mu) / sd

    best_corr = np.zeros((K, K), dtype=float)
    best_lag = np.zeros((K, K), dtype=int)
    for tau in range(1, max_lag + 1):
        x_prev = z[:-tau]            # (T-tau, K) : "cause" retardee
        y_next = z[tau:]             # (T-tau, K) : "effet"
        m = x_prev.shape[0]
        # correlation de Pearson vectorisee : (X^T Y) / m (colontes deja std)
        rho = (x_prev.T @ y_next) / m      # (K, K), rho[i, j] = corr(i -> j au lag tau)
        abs_rho = np.abs(rho)
        improve = abs_rho > np.abs(best_corr)
        best_corr = np.where(improve, rho, best_corr)
        best_lag = np.where(improve, tau, best_lag)
    np.fill_diagonal(best_corr, 0.0)
    np.fill_diagonal(best_lag, 0)
    return {"matrix": best_corr, "best_lag": best_lag, "max_lag": int(max_lag)}


def fanout_profile(
    infl: np.ndarray,
    z_threshold: float = 2.0,
) -> Dict[str, np.ndarray]:
    """Profil de **fan-out** par feature (Gate 22).

    Pour chaque feature source ``i``, compte combien de features cibles ``j``
    elle influence significativement, i.e. pour lesquelles
    ``|infl[i, j]|`` depasse ``z_threshold`` ecarts-types de la distribution de
    **toutes** les influences hors-diagonale. Un "hub" = feature a fan-out
    disproportionne.

    Parametres
    ----------
    infl : array (K, K)
        Matrice d'influence (sortie ``matrix`` de :func:`lagged_influence`).
    z_threshold : float
        Seil en ecarts-types au-dessus de la moyenne des |influences|
        hors-diagonale. ``z_threshold = 2.0`` (defaut) = top ~2.5 % d'une
        gaussienne ; ``1.0`` plus permissif, ``3.0`` plus strict.

    Retour
    ------
    dict
        ``fanout`` : array (K,) int, nombre de cibles significatives par source.
        ``strength`` : array (K,) float, somme des influences significatives par
        source (score continu, complementaire au compte). ``threshold`` : float,
        seuil absolu utilise (pour reproductibilite).
    """
    M = np.asarray(infl, dtype=float)
    K = M.shape[0]
    off = M[~np.eye(K, dtype=bool)]
    mu = float(off.mean()) if off.size else 0.0
    sd = float(off.std()) if off.size else 1.0
    if sd == 0.0:
        sd = 1.0
    abs_thr = abs(mu) + z_threshold * sd
    significant = np.abs(M) > abs_thr
    np.fill_diagonal(significant, False)
    fanout = significant.sum(axis=1).astype(int)
    strength = np.where(significant, np.abs(M), 0.0).sum(axis=1)
    return {"fanout": fanout, "strength": strength, "threshold": float(abs_thr)}


def workspace_candidates(
    fanout: np.ndarray,
    top_fraction: float = 0.1,
) -> Dict[str, object]:
    """Selectionne les **candidates workspace** (Gate 22, sous-ensemble a fan-out
    disproportionne).

    Analogue observationnel de la structure workspace d'Anthropic (un petit
    sous-ensemble, ~ <10 % du panel, a connectivite disproportionnee). Renvoie
    les indices tries par fan-out decroissant et un test honnete de
    **concentration anormale** : le coefficient de Gini du vecteur ``fanout``
    (un fan-out uniforme = Gini ~ 0 = pas de hub ; un fan-out concentre =
    Gini eleve = structure workspace detectee).

    Parametres
    ----------
    fanout : array (K,)
        Compte de fan-out par feature (sortie ``fanout`` de :func:`fanout_profile`).
        Accepte aussi un vecteur de ``strength`` continu -- la selection par
        rang est invariante.
    top_fraction : float
        Fraction du panel retenue, dans ``]0, 1]``. ``0.1`` (defaut) reflete le
        <10 % d'activite d'Anthropic (garde-fou : mesure, ne l'assume pas).

    Retour
    ------
    dict
        ``indices`` : array int, indices des top features tries par fan-out
        decroissant (LONGUEUR = ``ceil(top_fraction * K)``). ``scores`` : array
        float, leurs fan-out. ``n_selected`` : int. ``gini`` : float dans
        ``[0, 1]`` (concentration du fan-out). ``concentrated`` : bool,
        True si ``gini`` franchit un seuil empirique (0.2 par defaut, faible --
        a recalibrer sur les traces reelles ; c'est un drapeau, pas un verdict).
    """
    f = np.asarray(fanout, dtype=float).ravel()
    K = len(f)
    if K == 0:
        return {"indices": np.array([], dtype=int), "scores": np.array([]),
                "n_selected": 0, "gini": 0.0, "concentrated": False}
    if not 0.0 < top_fraction <= 1.0:
        raise ValueError(f"top_fraction dans ]0, 1] requis, got {top_fraction}")
    n_sel = max(1, int(np.ceil(top_fraction * K)))
    order = np.argsort(f)[::-1]
    indices = order[:n_sel]
    scores = f[indices]

    # Gini du vecteur fanout (concentration anormale ?) -- meme formule exacte
    # tri CROISSANT que concentration_series (cf. docstring).
    total = f.sum()
    if total > 0:
        p = f / total
        order_p = np.argsort(p)  # croissant
        p_sorted = p[order_p]
        weights = np.arange(1, K + 1, dtype=float)
        gini = 2.0 * (p_sorted * weights).sum() / K - (K + 1.0) / K
        gini_max = (K - 1.0) / K
        gini = float(np.clip(gini / gini_max if gini_max > 0 else 0.0, 0.0, 1.0))
    else:
        gini = 0.0
    return {
        "indices": indices.astype(int),
        "scores": scores,
        "n_selected": int(n_sel),
        "gini": gini,
        # seuil empirique faible : un fan-out uniforme donne Gini ~ 0 ;
        # 0.2 signale une concentration visible. A recalibrer sur traces reelles.
        "concentrated": bool(gini > 0.2),
    }


# --------------------------------------------------------------------------- #
# Batterie event-triggered (Gate 23 -- reutilise synthesis.emergence_gain)
# --------------------------------------------------------------------------- #
def event_triggered_battery(
    states: Sequence,
    events: Sequence[int],
    window: int,
    rng: np.random.Generator,
    n_shuffles: int = 20,
    neutral: Sequence[int] | None = None,
    n_neutral: int | None = None,
    unseen: str = "self",
) -> Dict:
    """Batterie d'emergence **event-triggered** (Gate 23, co-location IIT<->GWT).

    C'est le gate de **reconciliation** : les evenements d'acces global
    (ignitions) co-localisent-ils avec les pics de complexite integree
    creditee ? Pour chaque evenement, on extrait une fenetre centree dans la
    trajectoire discrete ``states`` et on lui applique
    :func:`ict.synthesis.emergence_gain` -- **VERBATIM** (meme rng, meme
    discipline de creditation au-dessus du controle shuffle). On contraste avec
    des fenetres neutres appariees hors-evenement.

    **Reutilise ``synthesis.emergence_gain`` par import, pas par copie** : la
    discipline de creditation (real > shuffled + 1 ecart-type) est exactement
    celle du capstone ICT-15, appliquee a l'identique. C'est l'invariant
    methodologique de la serie ICT -- un meme appareil sur tous les substrats.

    Parametres
    ----------
    states : sequence de labels hachables
        Trajectoire **deja discretisee** (coarse-graining substrat-specifique :
        ce choix vit dans le notebook, cf. :mod:`ict.synthesis`). La
        discretisation de ``acts`` (activations continues) en etats n'est PAS
        faite ici -- elle est un choix documente et mesure, pas une constante
        cachee.
    events : sequence d'int
        Indices **centres** des fenetres evenement (sortie ``center`` de
        :func:`ignition_events`, typiquement).
    window : int
        Demi-largeur de la fenetre centree. La fenetre est
        ``states[e-window : e+window]`` (longueur ``2*window``). Doit etre assez
        large pour porter une dynamique (>= 10) mais assez petite pour rester
        locale (<= quelques centaines).
    rng : np.random.Generator
        Generateur passe a ``emergence_gain`` (discipline commune rng).
    n_shuffles : int
        Nombre de permutations du controle shuffle (passe a ``emergence_gain``).
    neutral : sequence d'int, optionnel
        Indices des fenetres neutres appariees. Si None, on tire
        ``n_neutral`` centres uniformement hors d'une marge ``window`` autour de
        chaque evenement.
    n_neutral : int, optionnel
        Nombre de fenetres neutres a tirer si ``neutral is None`` (defaut :
        ``len(events)``).
    unseen : str
        Strategie d'etats non vus (passe a ``emergence_gain`` / TPM).

    Retour
    ------
    dict
        ``per_event`` : list de dicts ``emergence_gain`` (un par evenement).
        ``per_neutral`` : list de dicts ``emergence_gain`` (un par fenetre neutre).
        ``ec_gain_event`` : float, moyenne de ``ec_gain`` sur fenetres event.
        ``ec_gain_neutral`` : float, moyenne de ``ec_gain`` sur fenetres neutres.
        ``contrast`` : float, ``ec_gain_event - ec_gain_neutral`` (> 0 = les
        evenements portent plus d'emergence creditee que les fenetres neutres).
        ``fraction_credited_events`` : float, fraction des fenetres event dont
        ``emergence_gain`` renvoie ``credited=True``.
        ``fraction_credited_neutral`` : idem pour les neutres.
        ``n_events`` / ``n_neutral`` : int.
    """
    seq = list(states)
    T = len(seq)
    if window < 1:
        raise ValueError(f"window >= 1 requis, got {window}")

    def _extract(center: int) -> list:
        lo = max(0, center - window)
        hi = min(T, center + window)
        return seq[lo:hi]

    def _gain(center: int) -> dict:
        chunk = _extract(center)
        if len(chunk) < 3:
            # fenetre trop courte pour estimer une TPM : emergence indeterminee
            return {"ec_gain": 0.0, "ei_gain": 0.0, "credited": False,
                    "n_states": 0, "_short": True}
        return SYN.emergence_gain(chunk, rng, n_shuffles=n_shuffles, unseen=unseen)

    per_event = [_gain(int(e)) for e in events]

    # fenetres neutres : tirees hors d'une marge window autour de chaque event
    if neutral is None:
        target_n = n_neutral if n_neutral is not None else len(events)
        excluded = set()
        for e in events:
            for d in range(-window, window + 1):
                excluded.add(int(e) + d)
        available = [c for c in range(window, T - window) if c not in excluded]
        neutral_centers: List[int] = []
        if available and target_n > 0:
            idx = rng.choice(len(available), size=min(target_n, len(available)), replace=True)
            neutral_centers = [int(available[i]) for i in idx]
    else:
        neutral_centers = [int(c) for c in neutral]
    per_neutral = [_gain(c) for c in neutral_centers]

    def _mean_gain(rows: List[dict], key: str) -> float:
        vals = [r[key] for r in rows if not r.get("_short")]
        return float(np.mean(vals)) if vals else 0.0

    def _frac_credited(rows: List[dict]) -> float:
        rows_valid = [r for r in rows if not r.get("_short")]
        if not rows_valid:
            return 0.0
        return float(np.mean([bool(r.get("credited", False)) for r in rows_valid]))

    ec_ev = _mean_gain(per_event, "ec_gain")
    ec_nt = _mean_gain(per_neutral, "ec_gain")
    return {
        "per_event": per_event,
        "per_neutral": per_neutral,
        "ec_gain_event": ec_ev,
        "ec_gain_neutral": ec_nt,
        "contrast": float(ec_ev - ec_nt),
        "fraction_credited_events": _frac_credited(per_event),
        "fraction_credited_neutral": _frac_credited(per_neutral),
        "n_events": len(per_event),
        "n_neutral": len(per_neutral),
    }
