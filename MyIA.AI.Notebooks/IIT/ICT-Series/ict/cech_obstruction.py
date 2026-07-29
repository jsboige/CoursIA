"""Cochaîne de Čech pondérée -- l'obstruction entre proxys, intra-substrat (ICT #7744).

Contexte
--------
``ict.meta_proxy`` (PR #7578, « Phase Zéro ») détecte la **dispersion des
signatures entre substrats** : il compare les *niveaux bruts* des proxys
(spectral_gap, sensitivity_mean, ...) d'un substrat à l'autre. Le diagnostic
ferme de l'audit (tour 369, issue #7744) est que ce n'est pas une obstruction
entre proxys : comparer des niveaux bruts, même normalisés, mesure un écart
*d'échelle*, pas un *motif de désaccord structurel*.

Ce module corrige cela en remplaçant la comparaison de niveaux par des
**structures relationnelles internes** (rangs, transport, holonomie) portant
sur les proxys **d'un même substrat** -- et en lui donnant sa forme
mathématique minimale : une **cochaîne de Čech pondérée**.

L'objet candidat
----------------
On découpe la trajectoire d'un substrat en fenêtres ; chaque proxy devient
une **section locale** (sa valeur scalaire par fenêtre). Sur ces sections :

* **recouvrements doubles** (paires de proxys) = **résidu de transport** :
  ce qui reste du désaccord ``s_i − s_j`` après avoir retiré la meilleure
  relation affine ``(a·s_j + b)``. C'est le **cobord** (1-cochaîne) : un
  désaccord purement affine est *absorbé* par le cobord -- il n'est PAS une
  obstruction, juste un changement d'échelle/niveau.
* **recouvrements triples** (triplets de proxys) = **holonomie** : la somme
  cyclique des résidus ``r_ij + r_jk + r_ki``. C'est le **cocycle**
  (2-cochaîne) : si les sections proviennent d'une mesure globale cohérente,
  l'holonomie s'annule ; un désaccord *cyclique* (A>B, B>C, C>A) ne le peut
  pas -- c'est l'**obstruction**.
* **non-nullité stable de la classe** = cocycle / cobord : la fraction du
  désaccord qui n'est PAS expliquée par les relations affines par paires.
  Non-nulle + stable = l'obstruction expérimentale (#7395/#7744).

Hiérarchie de sobriété (garde-fou #7744)
----------------------------------------
On reste au niveau **« candidat à une obstruction »** : les 6 prérequis du
complexe de Čech sont réunis (base de contextes = fenêtres ; données locales
= sections ; restrictions = par-fenêtre ; résidus doubles = ``r_ij`` ;
cocycle triple = ``h_ijk`` ; quotient cobords = ``obstruction_ratio``) mais
on ne promeut pas vers stack/gerbe -- « un faisceau calculable est le bon
niveau de sobriété ».

Additif, indépendant de ``meta_proxy`` (Phase Zéro laissée intacte).
numpy seul, CPU.
"""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Mapping, Sequence

import numpy as np

# Proxy callable : (états d'une fenêtre, n_symbols) -> scalaire.
# Même signature que ict.meta_proxy.ProxyFn.
ProxyFn = Callable[[Sequence[int], int], float]


# --------------------------------------------------------------------------- #
#  1. Sections locales : un proxy par fenêtre                                   #
# --------------------------------------------------------------------------- #
def proxy_sections(
    states: Sequence[int],
    n_symbols: int,
    window_size: int,
    proxies: Mapping[str, ProxyFn],
) -> Dict[str, np.ndarray]:
    """Calcule la section locale de chaque proxy (valeur par fenêtre).

    Découpe ``states`` en fenêtres contiguës de ``window_size`` transitions
    (donc ``window_size + 1`` états) et évalue chaque proxy sur chaque
    fenêtre. Renvoie ``{nom_proxy: array[float]}`` de longueur
    ``n_windows``.

    Paramètres
    ----------
    states : trajectoire discrète (labels entiers dans ``[0, n_symbols)``).
    n_symbols : taille du vocabulaire.
    window_size : nombre de transitions par fenêtre (>= 1).
    proxies : dict ``{nom: callable}``. Au moins 2 proxys requis pour qu'un
        recouvrement ait un sens ; 3 pour un cocycle triple.

    Notes
    -----
    Les fenêtres sont non-recouvrantes (découpage contigu) : c'est le choix
    le plus sobre pour un « candidat » -- un découpage glissant produirait
    des sections corrélées par construction, masquant l'obstruction.
    """
    if n_symbols < 2:
        raise ValueError(f"n_symbols >= 2 requis (recu {n_symbols}).")
    if window_size < 1:
        raise ValueError(f"window_size >= 1 requis (recu {window_size}).")
    if len(proxies) < 2:
        raise ValueError(
            f">= 2 proxys requis pour un recouvrement (recu {len(proxies)})."
        )
    states_arr = np.asarray([int(s) for s in states], dtype=int)
    if states_arr.size < window_size + 1:
        raise ValueError(
            f"trajectoire trop courte ({states_arr.size} etats) pour "
            f"window_size={window_size} (>= {window_size + 1} requis)."
        )

    step = window_size  # fenêtres contiguës
    starts = np.arange(0, states_arr.size - window_size, step)
    sections: Dict[str, np.ndarray] = {}
    for name, fn in proxies.items():
        vals = np.empty(starts.size, dtype=float)
        for k, s0 in enumerate(starts):
            window = states_arr[s0 : s0 + window_size + 1]
            vals[k] = float(fn(window.tolist(), n_symbols))
        sections[name] = vals
    return sections


def normalize_sections(
    sections: Mapping[str, np.ndarray],
) -> Dict[str, np.ndarray]:
    """Centré-réduit chaque section (retire niveau + échelle bruts).

    C'est l'opération clé #7744 : on ne compare PAS les niveaux bruts (ce que
    fait Phase Zéro) mais la **structure relative** de chaque section. La
    moyenne retire le niveau (l'« échelle globale »), la norme retire
    l'amplitude. Ce qui reste est le *motif* de la section -- comparable
    entre proxys d'échelles différentes.
    """
    out: Dict[str, np.ndarray] = {}
    for name, s in sections.items():
        s = np.asarray(s, dtype=float)
        mu = s.mean()
        sigma = s.std()
        if sigma < 1e-12:
            # Section constante (proxy insensible aux fenêtres) -> vecteur 0.
            # Il n'y a pas de « structure relative » à comparer ; on laisse 0
            # pour que ce proxy ne contribue ni au cobord ni au cocycle.
            out[name] = np.zeros_like(s)
        else:
            out[name] = (s - mu) / sigma
    return out


def effective_dimensionality(
    sections: Mapping[str, np.ndarray],
    *,
    normalize: bool = True,
) -> Dict[str, float]:
    """Dimensionnalité effective du faisceau de sections (l'obstruction robuste).

    C'est la **mesure d'obstruction principale** du module. Les sections
    normalisées (une ligne par proxy) forment une matrice ``M`` dont la SVD
    révèle combien de dimensions latentes les proxys exploitent réellement :

    * **s2/s1 petit** : les proxys vivent dans un sous-espace affine de
      dimension 1 -- chacun est une fonction affine d'un **signal latent
      commun**. Ils se recollent en une **mesure globale unique** : pas
      d'obstruction (classe de cohomologie triviale).
    * **s2/s1 grand** : les proxys étalent >= 2 dimensions -- **aucun signal
      global unique** ne les réconcilie. C'est l'**obstruction** de Čech
      (classe non-triviale : les sections locales ne se globalisent pas).

    Pourquoi la SVD plutôt que l'holonomie brute ? Le signe par-fenêtre de
    l'holonomie oscille (~0.5 de cohérence, non-discriminant), alors que le
    rang effectif est un invariant stable. La SVD opérationnalise ici la
    non-trivialité de H¹ (obstruction au recollement global) dans le cas
    acyclique -- c'est le bon niveau de sobriété (#7744).

    Renvoie ``{s1, s2, s3, s2_over_s1, effective_rank}`` où ``effective_rank``
    = nombre de valeurs > ``rank_floor`` · s1.
    """
    secs = normalize_sections(sections) if normalize else dict(sections)
    if not secs:
        return {"s1": 0.0, "s2": 0.0, "s3": 0.0, "s2_over_s1": 0.0, "effective_rank": 0}
    M = np.vstack([np.asarray(secs[k], dtype=float) for k in secs])
    s = np.linalg.svd(M, compute_uv=False)
    s = np.maximum(s, 1e-12)
    s1 = float(s[0])
    s2 = float(s[1]) if len(s) > 1 else 0.0
    s3 = float(s[2]) if len(s) > 2 else 0.0
    rank_floor = 0.1  # une valeur < 10% de s1 = négligeable.
    eff_rank = int(np.sum(s >= rank_floor * s1))
    return {
        "s1": s1,
        "s2": s2,
        "s3": s3,
        "s2_over_s1": s2 / s1,
        "effective_rank": eff_rank,
    }


# --------------------------------------------------------------------------- #
#  2. Cobord (1-cochaîne) : résidu de transport sur recouvrement double        #
# --------------------------------------------------------------------------- #
def transport_residual(
    s_i: np.ndarray,
    s_j: np.ndarray,
) -> Dict[str, Any]:
    """Résidu de transport entre deux sections (cobord de Čech, 1-cochaîne).

    Ajuste la meilleure relation affine ``s_i ~ a·s_j + b`` (moindres
    carrés) et renvoie le résidu ``r = s_i - (a·s_j + b)`` : ce qui du
    désaccord ``s_i - s_j`` n'est PAS expliqué par un simple changement
    d'échelle/niveau. Ce résidu est le **cobord** -- un désaccord purement
    affine est absorbé (résidu ~ 0) et n'est donc PAS une obstruction.

    Renvoie
    -------
    dict avec ``residual`` (array par-fenêtre), ``a``, ``b`` (affine),
    ``norm`` (norme L2 du résidu), ``cosine`` (similarité structurelle :
    1 = même motif, 0 = indépendant).
    """
    s_i = np.asarray(s_i, dtype=float)
    s_j = np.asarray(s_j, dtype=float)
    if s_i.shape != s_j.shape:
        raise ValueError(
            f"sections de formes differentes : {s_i.shape} vs {s_j.shape}"
        )
    if s_i.size < 2:
        raise ValueError(f">= 2 fenêtres requis pour un ajustement affine.")

    # Moindres carrés : a = cov(i,j)/var(j), b = mean(i) - a*mean(j).
    var_j = s_j.var()
    if var_j < 1e-12:
        # s_j constant après normalisation -> pas de relation affine définie.
        # Le résidu = s_i lui-même (rien n'est expliqué par s_j).
        a = 0.0
        b = float(s_i.mean())
    else:
        a = float(np.mean((s_i - s_i.mean()) * (s_j - s_j.mean())) / var_j)
        b = float(s_i.mean() - a * s_j.mean())
    residual = s_i - (a * s_j + b)
    norm = float(np.sqrt(np.mean(residual ** 2)))
    # Cosinus de similarité structurelle (sur les centrés).
    ci = s_i - s_i.mean()
    cj = s_j - s_j.mean()
    denom = np.sqrt(np.mean(ci ** 2)) * np.sqrt(np.mean(cj ** 2))
    cosine = float(np.mean(ci * cj) / denom) if denom > 1e-12 else 0.0
    return {"residual": residual, "a": a, "b": b, "norm": norm, "cosine": cosine}


# --------------------------------------------------------------------------- #
#  3. Cocycle (2-cochaîne) : holonomie sur recouvrement triple                 #
# --------------------------------------------------------------------------- #
def holonomy(
    r_ij: np.ndarray,
    r_jk: np.ndarray,
    r_ki: np.ndarray,
) -> Dict[str, float]:
    """Holonomie d'un triplet de proxys (cocycle de Čech, 2-cochaîne).

    La somme cyclique ``h = r_ij + r_jk + r_ki`` mesurée par fenêtre. Si les
    trois résidus proviennent de sections cohérentes (un même global sous-
    jacent), l'holonomie s'annule. Un désaccord *cyclique* -- où la structure
    de i vs j, j vs k et k vs i ne se recolle pas -- laisse une holonomie
    non-nulle : c'est l'**obstruction** (la classe ne se trivialise pas dans
    le quotient cobords).

    Renvoie
    -------
    dict avec ``holonomy`` (norme RMS par fenêtre), ``max_abs`` (pire fenêtre),
    ``sign_consistency`` (fraction de fenêtres de même signe -- une holonomie
    stable a une signature de signe cohérente, vs un bruit qui oscille).
    """
    r_ij = np.asarray(r_ij, dtype=float)
    r_jk = np.asarray(r_jk, dtype=float)
    r_ki = np.asarray(r_ki, dtype=float)
    h = r_ij + r_jk + r_ki
    rms = float(np.sqrt(np.mean(h ** 2)))
    max_abs = float(np.max(np.abs(h))) if h.size else 0.0
    # Sign-consistency : stabilité du signe (une obstruction a un signe
    # dominant ; un résidu de bruit oscille autour de 0).
    if h.size:
        pos = float(np.mean(h > 1e-9))
        neg = float(np.mean(h < -1e-9))
        sign_consistency = max(pos, neg)
    else:
        sign_consistency = 0.0
    return {
        "holonomy": rms,
        "max_abs": max_abs,
        "sign_consistency": sign_consistency,
    }


# --------------------------------------------------------------------------- #
#  4. Classe d'obstruction + verdict falsifiable                                #
# --------------------------------------------------------------------------- #
def cech_obstruction_class(
    sections: Mapping[str, np.ndarray],
    *,
    normalize: bool = True,
) -> Dict[str, Any]:
    """Classe d'obstruction de Čech sur un jeu de sections de proxys.

    Calcule tous les cobords par paires (résidus de transport) et tous les
    cocycles par triplets (holonomies), puis le rapport cocycle/cobord :
    la fraction du désaccord qui n'est PAS expliquée par les relations
    affines par paires. C'est la **mesure d'obstruction** #7744.

    Paramètres
    ----------
    sections : ``{nom_proxy: array}``. >= 2 pour le cobord, >= 3 pour le
        cocycle (sinon le cocycle est absent et l'obstruction reste 0).
    normalize : centrer-réduire les sections d'abord (défaut True -- on
        compare la structure relative, pas les niveaux bruts).

    Renvoie
    -------
    dict avec :
      * ``n_proxies``, ``n_windows`` ;
      * ``pairwise_residuals`` : ``{(i,j): norm}`` du cobord ;
      * ``mean_coboundary`` : moyenne des normes de résidus (désaccord total) ;
      * ``triple_holonomies`` : ``{(i,j,k): holonomy}`` du cocycle ;
      * ``mean_cocycle`` : moyenne des holonomies (partie obstructive) ;
      * ``obstruction_ratio`` : ``mean_cocycle / (mean_coboundary + eps)`` ;
      * ``sign_consistency`` : moyenne sur les triplets (stabilité du signe).
    """
    secs = normalize_sections(sections) if normalize else dict(sections)
    names = list(secs.keys())
    n = len(names)

    pairwise: Dict[tuple, float] = {}
    residuals: Dict[tuple, np.ndarray] = {}
    for a in range(n):
        for b in range(a + 1, n):
            ij = (names[a], names[b])
            res = transport_residual(secs[names[a]], secs[names[b]])
            pairwise[ij] = res["norm"]
            residuals[ij] = res["residual"]
    mean_coboundary = float(np.mean(list(pairwise.values()))) if pairwise else 0.0

    triples: Dict[tuple, float] = {}
    sign_cons: List[float] = []
    if n >= 3:
        for a in range(n):
            for b in range(a + 1, n):
                for c in range(b + 1, n):
                    ijk = (names[a], names[b], names[c])
                    r_ab = residuals[(names[a], names[b])]
                    r_bc = residuals[(names[b], names[c])]
                    # paire (c,a) : reconstruire dans le bon ordre.
                    key_ca = (names[a], names[c]) if (names[a], names[c]) in residuals else (names[c], names[a])
                    r_ca = residuals[key_ca]
                    # Holonomie cyclique : r(a,b) + r(b,c) + r(c,a).
                    # r(c,a) depuis la paire stockée (a,c) : si stockée comme
                    # (a,c) c'est residual(a,c)=a-(a·c+b) i.e. "a vs c" ;
                    # cycliquement on veut c-vs-a = -residual(a,c) approximé
                    # par symétrie du résidu structurel (après normalisation
                    # le résidu est anti-symétrique en signe près).
                    if (names[c], names[a]) in residuals:
                        r_ca = residuals[(names[c], names[a])]
                    else:
                        r_ca = -residuals[(names[a], names[c])]
                    h = holonomy(r_ab, r_bc, r_ca)
                    triples[ijk] = h["holonomy"]
                    sign_cons.append(h["sign_consistency"])
    mean_cocycle = float(np.mean(list(triples.values()))) if triples else 0.0
    sign_consistency = float(np.mean(sign_cons)) if sign_cons else 0.0

    eps = 1e-12
    obstruction_ratio = mean_cocycle / (mean_coboundary + eps)
    dim = effective_dimensionality(secs, normalize=False)  # déjà normalisées.

    return {
        "n_proxies": n,
        "n_windows": int(len(next(iter(secs.values())))) if secs else 0,
        "pairwise_residuals": pairwise,
        "mean_coboundary": mean_coboundary,
        "triple_holonomies": triples,
        "mean_cocycle": mean_cocycle,
        "obstruction_ratio": obstruction_ratio,
        "sign_consistency": sign_consistency,
        "effective_rank": dim["effective_rank"],
        "s2_over_s1": dim["s2_over_s1"],
    }


def cech_obstruction_verdict(
    report: Mapping[str, Any],
    *,
    dim_threshold: float = 0.10,
    coboundary_floor: float = 0.05,
) -> str:
    """Verdict falsifiable sur la classe d'obstruction.

    Mesure primaire : la **dimensionnalité effective** (``s2_over_s1``). Les
    proxys se recollent en une mesure globale unique ssi ils vivent en
    dimension 1 (``s2/s1`` petit) ; sinon l'obstruction est non-triviale.

    Paramètres
    ----------
    report : sortie de :func:`cech_obstruction_class`.
    dim_threshold : ``s2/s1`` au-dessus duquel la dimension 2 devient
        significative -> obstruction non-triviale (défaut 0.10).
    coboundary_floor : ``mean_coboundary`` sous lequel les proxys sont
        affinement cohérents (aucun désaccord à obstructer) -> TRIVIAL quoi
        qu'il arrive (défaut 0.05).

    Verdicts
    --------
    * ``NON_TRIVIAL`` : ``s2/s1 > dim_threshold`` ET ``mean_coboundary >
      floor`` -- les proxys ne se réduisent pas à un signal latent unique,
      obstruction candidate (#7744 acceptance positive).
    * ``TRIVIAL`` : ``mean_coboundary <= floor`` (proxys affinement cohérents,
      la classe se trivialise -- une différence d'échelle n'est PAS une
      obstruction, c'est la confusion de Phase Zéro) OU ``s2/s1 <= threshold``.
    * ``INCONCLUSIVE`` : < 3 proxys (pas de cocycle triple défini).
    """
    if report["n_proxies"] < 3:
        return "INCONCLUSIVE"
    cob = float(report["mean_coboundary"])
    s2s1 = float(report["s2_over_s1"])
    if cob <= coboundary_floor:
        return "TRIVIAL"
    if s2s1 > dim_threshold:
        return "NON_TRIVIAL"
    return "TRIVIAL"


# --------------------------------------------------------------------------- #
#  5. Banc d'essai falsifiable (protocole #7744)                                #
# --------------------------------------------------------------------------- #
def cech_obstruction_test(
    n_windows: int = 60,
    seed: int = 0,
) -> Dict[str, Any]:
    """Banc falsifiable : TRIVIAL (1D affine) vs NON_TRIVIAL (>=2D).

    Construit deux jeux de 3 proxys :

    * **Affine (1D)** : chaque proxy est une transformation affine d'un signal
      latent commun (échelles/niveaux/signes différents). Tous vivent en
      dimension 1 -> ils se recollent en une mesure globale unique ->
      verdict ``TRIVIAL``. C'est précisément le cas que Phase Zéro
      (``meta_proxy``) confond avec une obstruction : une différence
      d'échelle n'est PAS une obstruction.
    * **Multi-dimensionnel (>=2D)** : deux proxys suivent deux signaux
      latents indépendants, le troisième un mélange. Aucun signal global
      unique ne les réconcilie -> verdict ``NON_TRIVIAL``.

    Verdict falsifiable
    -------------------
    ``passes`` est True ssi le banc affine rend ``TRIVIAL`` ET le banc
    multi-dimensionnel rend ``NON_TRIVIAL``. Un outil qui classerait les deux
    ``NON_TRIVIAL`` reproduirait la confusion de Phase Zéro ; un outil qui
    classerait les deux ``TRIVIAL`` est aveugle à l'obstruction réelle.
    """
    rng = np.random.default_rng(seed)

    # --- Banc affine (1D) : 3 proxys = a*latent + b. ---
    latent = rng.standard_normal(n_windows)
    affine_sections = {
        "A": 2.5 * latent + 10.0,
        "B": -0.8 * latent - 3.0,
        "C": 1.3 * latent + 7.0,
    }
    rep_aff = cech_obstruction_class(affine_sections)
    verdict_aff = cech_obstruction_verdict(rep_aff)

    # --- Banc multi-dimensionnel (>=2D) : 2 latents indépendants. ---
    x = rng.standard_normal(n_windows)
    y = rng.standard_normal(n_windows)
    multi_sections = {
        "A": x,
        "B": y,
        "C": x + y,  # mélange : vit dans le plan (x,y), pas sur une droite.
    }
    rep_mul = cech_obstruction_class(multi_sections)
    verdict_mul = cech_obstruction_verdict(rep_mul)

    passes = verdict_aff == "TRIVIAL" and verdict_mul == "NON_TRIVIAL"
    return {
        "affine_s2_over_s1": rep_aff["s2_over_s1"],
        "affine_coboundary": rep_aff["mean_coboundary"],
        "affine_verdict": verdict_aff,
        "multi_s2_over_s1": rep_mul["s2_over_s1"],
        "multi_coboundary": rep_mul["mean_coboundary"],
        "multi_effective_rank": rep_mul["effective_rank"],
        "multi_verdict": verdict_mul,
        "passes": 1.0 if passes else 0.0,
    }


__all__ = [
    "ProxyFn",
    "proxy_sections",
    "normalize_sections",
    "effective_dimensionality",
    "transport_residual",
    "holonomy",
    "cech_obstruction_class",
    "cech_obstruction_verdict",
    "cech_obstruction_test",
]
