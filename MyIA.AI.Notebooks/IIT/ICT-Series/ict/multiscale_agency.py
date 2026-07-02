"""Agence morphologique **multi-echelles** (notebook ICT-11).

Prolonge la mesure d'agence d'ICT-9 (cf. :mod:`ict.agency` : ``repair_gain``,
``time_to_recover``, ``basin_return_probability`` sur un champ de Gray-Scott
ablate) en posant la question centrale de la strate 3 :

    **A quelle echelle spatiale l'agence est-elle la plus lisible ?**

Le principe directeur reste « sans complaisance » : on ne DECLARE pas
d'echelle privilegiee, on la CHERCHE, et l'on accepte le verdict honnete
« pas de granularite privilegiee detectee sur ce systeme » si aucune courbe
d'agence ne presente de pic meso identifiable (cf. gate 1 de l'issue #4877).

Couplage causal (Hoel) — le pont champs -> TPM
----------------------------------------------
Les mesures d'agence operent sur des champs (U, V) ; la mesure causale
``effective_information`` de :mod:`ict.causal_emergence` opere sur une TPM
etat-a-etat. Pour les raccorder (gate 2), on construit, a chaque echelle
spatiale ``b`` (taille de bloc de moyennage), une **macro-variable scalaire** :

    X_t(b) = nombre de blocs « actifs » (moyenne de V superieure a un seuil)
             lorsque le champ est moyenne par blocs de cote ``b``.

Cette macro-variable est discretisee en un petit nombre de niveaux ; la
trajectoire de recuperation post-ablation (plusieurs graines poolees via
:mod:`ict.tpm_estimation`) fournit une TPM empirique. On calcule alors
:func:`ict.causal_emergence.effectiveness` — la primitive **scale-free**
(determinisme moins degenerescence, dans [0, 1]), choisie plutot que l'EI en
bits pour eviter l'artefact du ``log2(n)`` qui retrecit mecaniquement la mesure
aux echelles grossieres. La these de Hoel (« la macro-echelle peut avoir plus
de pouvoir causal que la micro ») est testee comme une **correlation
EI(echelle) <-> agence(echelle)** explicitement chiffree, jamais comme une
narration.

Meme intervention qu'ICT-9, resolue differemment
-------------------------------------------------
La meme intervention ``do(ablation)`` qu'ICT-9 est appliquee **pleine
resolution** (sur le champ natif). Seule la **resolution de mesure** varie
entre echelles : on moyenne le champ par blocs AVANT de mesurer. C'est la
condition du gate 3 : un controle qui varie avec l'echelle (une ablation plus
grossiere aux grandes echelles) invaliderait la comparaison inter-echelles.

Toutes les fonctions sont pures (numpy, CPU uniquement). Aucune n'invoque ni
ne suppose de « but » : le gel GPU est respecte.
"""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

import numpy as np

from . import agency as A
from . import causal_emergence as CE
from . import tpm_estimation as T


# --------------------------------------------------------------------------- #
# Coarse-graining spatial : moyenne par blocs
# --------------------------------------------------------------------------- #
def block_average(field: np.ndarray, block: int) -> np.ndarray:
    """Moyenne un champ 2D carre par blocs de cote ``block``.

    Un champ ``(n, n)`` devient ``(g, g)`` avec ``g = n // block`` ; chaque
    super-cellule est la moyenne arithmetique des ``block * block`` pixels qu'elle
    couvre. La portion restante (si ``block`` ne divise pas ``n``) est tronquee :
    c'est un coarse-graining spatial strict, la « resolution d'observation » du
    motif a l'echelle ``block``.

    Lever ``ValueError`` si ``block < 1`` ou si la grille resultante serait vide.
    """
    if block < 1:
        raise ValueError(f"block doit etre >= 1, recu {block}")
    f = np.asarray(field, dtype=float)
    n = f.shape[0]
    g = n // block
    if g < 1:
        raise ValueError(f"block={block} trop grand pour une grille n={n}")
    f = f[: g * block, : g * block]
    return f.reshape(g, block, g, block).mean(axis=(1, 3))


def downsample_mask(mask: np.ndarray, block: int) -> np.ndarray:
    """Projette un masque ``(n, n)`` sur la grille des super-cellules ``(g, g)``.

    Un bloc est marque ``True`` si la fraction de ses pixels couverts par le
    masque depasse la moitie. Utilise pour mesurer la recuperation **dans la
    region ablatee** a l'echelle ``block`` (meme region, plus de pixels moyens).
    """
    m = np.asarray(mask, dtype=float)
    return block_average(m, block) > 0.5


# --------------------------------------------------------------------------- #
# Macro-variable pour le raccord Hoel (gate 2) : structure a l'echelle
# --------------------------------------------------------------------------- #
def structure_at_scale(field: np.ndarray, block: int) -> float:
    """Quantite de structure spatiale du champ a l'echelle ``block``.

    C'est la variance (cf. :func:`ict.agency.structure`) du champ **moyenne par
    blocs** de cote ``block`` : un scalaire qui mesure « combien de motif il y
    a a cette resolution ». C'est la **macro-variable scalaire** du raccord Hoel
    (gate 2), choisie pour trois proprietes :

      1. **depend de l'echelle** : le moyennage par blocs reduit la variance
         (les fluctuations intra-bloc sont moyennees), donc la valeur decroit
         quand ``block`` augmente — contrairement a la moyenne globale, invariante
         par coarse-graining, qui ne pourrait pas distinguer les echelles ;
      2. **non saturante** : pendant la recuperation, la structure a l'echelle
         ``block`` passe d'une valeur basse (region ablatee) a la valeur de
         reference — elle traverse donc plusieurs niveaux, ce qui produit une TPM
         **non triviale** a toutes les echelles (cf. CI du gate 2) ;
      3. **directement couplee a l'agence** : c'est la grandeur meme dont
         :func:`agency_measures_at_scale` mesure la restauration, donc le raccord
         EI(echelle) <-> agence(echelle) porte sur la meme quantite.
    """
    return float(np.var(block_average(field, block)))


def discretize_values(values: np.ndarray, n_bins: int) -> np.ndarray:
    """Discretise une serie continue en ``n_bins`` niveaux (quantiles) -> entiers.

    Les bornes sont tirees des quantiles de la serie observee, dedupliquees ; on
    en deduit les **coupures interieures** et l'on attribue chaque valeur a un
    intervalle (``np.digitize``). Cas limites traites : serie constante ou
    quasi -> un seul niveau (0) ; serie a deux valeurs distinctes -> deux
    niveaux. Retourne des entiers ``0..n_bins-1`` preservant l'ordre (valeurs
    croissantes -> labels croissants).
    """
    v = np.asarray(values, dtype=float)
    n_bins = max(2, int(n_bins))
    if v.size < 2 or np.allclose(v, v[0]):
        return np.zeros(v.shape, dtype=int)
    edges = np.unique(np.quantile(v, np.linspace(0.0, 1.0, n_bins + 1)))
    if edges.size < 2:
        return np.zeros(v.shape, dtype=int)
    cuts = edges[1:-1] if edges.size >= 3 else edges[1:]
    labels = np.digitize(v, cuts)  # 0..len(cuts)
    return np.clip(labels, 0, n_bins - 1).astype(int)


# --------------------------------------------------------------------------- #
# Mesures d'agence a une echelle donnee (gate 1)
# --------------------------------------------------------------------------- #
def recovery_curve_at_scale(
    V_ref: np.ndarray,
    V_abl: np.ndarray,
    snapshots: List[np.ndarray],
    mask: np.ndarray,
    block: int,
) -> List[float]:
    """Courbe de recuperation (RD) a l'echelle ``block`` le long des snapshots.

    Pour chaque snapshot (champ ``V`` pleine resolution a un instant de la
    trajectoire de recuperation), on moyenne par blocs puis on evalue
    :func:`ict.agency.recovery_score` dans la region ``mask`` projettee a la
    meme echelle. Retourne la liste des scores de recuperation (un par snapshot).
    """
    V_ref_b = block_average(V_ref, block)
    V_abl_b = block_average(V_abl, block)
    mask_b = downsample_mask(mask, block)
    out: List[float] = []
    for snap in snapshots:
        s_b = block_average(snap, block)
        out.append(A.recovery_score(V_ref_b, V_abl_b, s_b, mask_b))
    return out


def agency_measures_at_scale(
    model_rd,
    model_diff_D: float,
    U_ref: np.ndarray,
    V_ref: np.ndarray,
    mask: np.ndarray,
    block: int,
    steps: int,
    record_every: int,
    tol: float = 0.1,
) -> Dict[str, float]:
    """Mesures d'agence canoniques d'ICT-9, resolutees a l'echelle ``block``.

    Protocol identique a ICT-9 (gate 3) :

      1. ``do(ablation)`` du masque ``mask`` **pleine resolution** -> ``U_abl, V_abl`` ;
      2. monde de reaction-diffusion : integration ``steps``, snapshots tous les
         ``record_every`` pas (etat ablate inclus en tete) ;
      3. monde de diffusion pure (contrefactuel) : integration ``steps`` sur le
         champ ``V_abl`` ;
      4. **moyennage par blocs** de tous les champs a l'echelle ``block``, puis
         mesure de :func:`ict.agency.recovery_score` et
         :func:`ict.agency.repair_gain` dans la region ablatee projettee.

    Retourne un dict :

      - ``repair_gain`` : recuperation(RD) - recuperation(diff), la mesure d'agence ;
      - ``recovery_RD`` : fraction de structure restauree par le monde RD ;
      - ``recovery_diff`` : idem pour le controle passif (diffusion seule) ;
      - ``time_to_recover`` : premier pas ou la structure regionale repasse au
        dessus de la cible (``None`` si jamais atteint) ;
      - ``target_structure`` : variance de reference dans la region ablatee.
    """
    U_abl, V_abl = A.ablate(U_ref, V_ref, mask)
    _, _, snaps = model_rd.run(
        U_abl, V_abl, steps, record_every=record_every, include_initial=True
    )
    from .reaction_diffusion import run_pure_diffusion

    V_diff_end = run_pure_diffusion(V_abl, model_diff_D, steps)

    V_ref_b = block_average(V_ref, block)
    V_abl_b = block_average(V_abl, block)
    V_diff_b = block_average(V_diff_end, block)
    mask_b = downsample_mask(mask, block)

    rec_RD_final = A.recovery_score(V_ref_b, V_abl_b, block_average(snaps[-1], block), mask_b)
    rec_diff_final = A.recovery_score(V_ref_b, V_abl_b, V_diff_b, mask_b)

    # courbe de structure regionale pour time_to_recover (echelle 'block')
    target = float(np.var(V_ref_b[mask_b])) if mask_b.any() else float(np.var(V_ref_b))
    structures_b = [
        float(np.var(block_average(s, block)[mask_b])) if mask_b.any()
        else float(np.var(block_average(s, block)))
        for s in snaps
    ]
    ttr = A.time_to_recover(structures_b, target, tol=tol, record_every=record_every)

    return {
        "repair_gain": A.repair_gain(rec_RD_final, rec_diff_final),
        "recovery_RD": rec_RD_final,
        "recovery_diff": rec_diff_final,
        "time_to_recover": ttr,
        "target_structure": target,
    }


def basin_return_at_scale(
    model,
    U_ref: np.ndarray,
    V_ref: np.ndarray,
    make_mask: Callable[[np.random.Generator], np.ndarray],
    block: int,
    steps: int,
    target_structure: float,
    tol: float = 0.2,
    n_trials: int = 5,
    rng: Optional[np.random.Generator] = None,
) -> float:
    """Probabilite de retour au bassin a l'echelle ``block`` (mesure stochastique).

    Variante de :func:`ict.agency.basin_return_probability` ou la structure finale
    est mesuree sur le champ **moyenne par blocs** (et non pleine resolution) :
    la cible de retour est donc elle-meme a l'echelle ``block``. On compte un
    succes si la structure regionale (variance du champ moyenne) revient dans
    ``[target_structure*(1-tol), target_structure*(1+tol)]``.

    AVERTISSEMENT (honnetete) : comme pour :func:`ict.agency.basin_return_probability`,
    cette mesure est stochastique et couteuse (une simulation complete par
    essai) ; avec peu d'essais l'estimation a une forte variance. Le notebook
    l'utilise avec un ``n_trials`` modeste et le documente comme tel.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    successes = 0
    lo = target_structure * (1.0 - tol)
    hi = target_structure * (1.0 + tol)
    for _ in range(n_trials):
        mask = make_mask(rng)
        U0, V0 = A.ablate(U_ref, V_ref, mask)
        _, V_end, _ = model.run(U0, V0, steps)
        s = float(np.var(block_average(V_end, block)))
        if lo <= s <= hi:
            successes += 1
    return successes / float(n_trials)


# --------------------------------------------------------------------------- #
# Raccord Hoel : TPM de la macro-variable a une echelle (gate 2)
# --------------------------------------------------------------------------- #
def structure_trajectory_at_scale(
    snapshots: List[np.ndarray],
    block: int,
) -> np.ndarray:
    """Trajectoire (continue) de la macro-variable ``structure(b)``.

    ``X_t(b) = structure_at_scale(snapshot_t, block)`` = variance du champ
    moyenne par blocs a l'instant t. C'est la grandeur dont on estime la TPM
    empirique (apres discretisation) pour le raccord Hoel (gate 2). Retourne un
    tableau 1-D de flottants (un par snapshot).
    """
    return np.array([structure_at_scale(s, block) for s in snapshots], dtype=float)


def effectiveness_at_scale(
    model,
    U_ref: np.ndarray,
    V_ref: np.ndarray,
    make_mask: Callable[[np.random.Generator], np.ndarray],
    block: int,
    steps: int,
    record_every: int,
    n_bins: int = 12,
    n_seeds: int = 4,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, object]:
    """Effectiveness (Hoel) de la dynamique de recuperation a l'echelle ``block``.

    Lance ``n_seeds`` trajectoires de recuperation depuis des ablations tirees
    par ``make_mask`` ; pour chacune, on extrait la trajectoire de la
    macro-variable ``structure(b)`` (variance du champ moyenne par blocs),
    discretisee en ``n_bins`` niveaux (quantiles, cf. :func:`discretize_values`).
    Les transitions des ``n_seeds`` trajectoires sont POOLEES pour estimer une
    TPM empirique robuste (:func:`ict.tpm_estimation.tpm_from_trajectories`),
    dont on calcule :

      - ``effectiveness`` : determinisme - degenerescence (scale-free, dans [0,1]) ;
      - ``effective_information`` : effectiveness * log2(n) en bits (reporte, mais
        NON utilise pour la correlation inter-echelles a cause de l'artefact log2(n)) ;
      - ``n_observed`` : nombre d'etats macro effectivement visites (>= 2 requis
        pour une TPM non triviale ; le notebook filtre les echelles degenerrees) ;
      - ``tpm`` : la TPM empirique (n_observed x n_observed).

    Le pooling multi-graines reduit (sans l'annuler) le bruit d'une TPM estimee
    sur peu de transitions ; le caveat est documente dans le notebook.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    trajectories: List[np.ndarray] = []
    for _ in range(n_seeds):
        mask = make_mask(rng)
        U0, V0 = A.ablate(U_ref, V_ref, mask)
        _, _, snaps = model.run(
            U0, V0, steps, record_every=record_every, include_initial=True
        )
        raw = structure_trajectory_at_scale(snaps, block)
        trajectories.append(discretize_values(raw, n_bins))
    tpm, mapping = T.tpm_from_trajectories([list(t) for t in trajectories])
    return {
        "effectiveness": CE.effectiveness(tpm),
        "effective_information": CE.effective_information(tpm),
        "n_observed": int(tpm.shape[0]),
        "tpm": tpm,
        "trajectories": trajectories,
    }


# --------------------------------------------------------------------------- #
# Statistique de raccord (gate 2)
# --------------------------------------------------------------------------- #
def pearson_corr(x: List[float], y: List[float]) -> Tuple[Optional[float], int]:
    """Correlation lineaire de Pearson entre deux series, avec garde-fous.

    Retourne ``(r, n)`` ou ``r`` est le coefficient (dans [-1, 1]), ``n`` la
    taille commune. Retourne ``(None, n)`` si la variance est nulle ou ``n < 2``
    — la correlation n'est alors pas definie, et le notebook le dit honnetement
    plutot que de produire un nombre trompeur.
    """
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    n = int(min(x.size, y.size))
    if n < 2:
        return None, n
    x = x[:n]
    y = y[:n]
    sx, sy = float(np.std(x)), float(np.std(y))
    if sx < 1e-12 or sy < 1e-12:
        return None, n
    xm, ym = x - x.mean(), y - y.mean()
    r = float(np.dot(xm, ym) / (np.sqrt(np.dot(xm, xm)) * np.sqrt(np.dot(ym, ym)) + 1e-12))
    return float(np.clip(r, -1.0, 1.0)), n
