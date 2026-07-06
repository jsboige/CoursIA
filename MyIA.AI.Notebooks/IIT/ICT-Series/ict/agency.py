"""Mesures d'**agence morphologique** : reparation de forme apres ablation.

Outille le notebook **ICT-9**. Le mot *agence* y est employe au sens strict et
**operationnel** de la litterature de la morphogenese et de la cognition basale
(M. Levin ; Mordvintsev et al., *Growing Neural Cellular Automata*, Distill
2020) : un systeme manifeste de l'agence sur sa propre forme s'il **repare** une
structure endommagee en revenant vers un point de consigne **intrinseque**,
plutot que de se laisser passivement evoluer.

Principe directeur (« sans complaisance ») : **l'agence n'est jamais declaree,
elle est mesuree** — et toujours **par contraste** avec des controles passifs.
On n'attribue d'agence a un systeme que si sa trajectoire de recuperation
**domine quantitativement** celle d'un controle prive du mecanisme reparateur.
C'est exactement le cadre du **calcul causal de Pearl** (*do-calculus*) : on
compare deux mondes contrefactuels issus de la **meme** intervention ``do(ablation)``,
l'un sous reaction-diffusion, l'autre sous diffusion seule.

Toutes les mesures sont des fonctions pures sur des champs ``numpy`` ; aucune ne
suppose ni n'invoque la moindre « intention ».
"""

from __future__ import annotations

from typing import Callable, List, Optional, Tuple

import numpy as np

# --------------------------------------------------------------------------- #
# Regions d'ablation
# --------------------------------------------------------------------------- #


def quadrant_mask(n: int, quadrant: int = 0) -> np.ndarray:
    """Masque booleen ``(n, n)`` couvrant un quart de la grille.

    ``quadrant`` : 0 = haut-gauche, 1 = haut-droit, 2 = bas-gauche, 3 = bas-droit.
    """
    mask = np.zeros((n, n), dtype=bool)
    h = n // 2
    rows = slice(0, h) if quadrant in (0, 1) else slice(h, n)
    cols = slice(0, h) if quadrant in (0, 2) else slice(h, n)
    mask[rows, cols] = True
    return mask


def disk_mask(n: int, cx: float, cy: float, radius: float) -> np.ndarray:
    """Masque booleen ``(n, n)`` d'un disque de centre ``(cx, cy)`` et rayon ``radius``."""
    yy, xx = np.mgrid[0:n, 0:n]
    return (xx - cx) ** 2 + (yy - cy) ** 2 <= radius ** 2


def ablate(
    U: np.ndarray,
    V: np.ndarray,
    mask: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray]:
    """Applique ``do(ablation)`` : reinitialise la region ``mask`` a l'etat nu.

    L'etat nu est l'etat de fond du substrat de Gray-Scott (``U = 1``, ``V = 0``),
    c'est-a-dire « pas de motif ici ». C'est l'**intervention** au sens de Pearl :
    on force une partie de l'etat, puis on observe la trajectoire qui en decoule.
    Retourne de **nouveaux** tableaux (n'altere pas les entrees).
    """
    U2 = U.copy()
    V2 = V.copy()
    U2[mask] = 1.0
    V2[mask] = 0.0
    return U2, V2


# --------------------------------------------------------------------------- #
# Mesures de structure et de distance morphologique
# --------------------------------------------------------------------------- #


def structure(V: np.ndarray) -> float:
    """Quantite de structure spatiale presente dans le champ ``V``.

    Mesuree par la **variance spatiale** : un champ uniforme (lisse, sans motif)
    a une variance nulle ; un champ structure (taches contrastees) a une variance
    positive. C'est l'indicateur le plus simple et le plus honnete de « il y a un
    motif ici » — il chute vers zero quand une forme se dissout.
    """
    return float(np.var(V))


def local_structure(V: np.ndarray, mask: np.ndarray) -> float:
    """Structure spatiale restreinte a une region (masque booleen).

    Variance de ``V`` sur les seules cellules selectionnees par ``mask`` (un
    tableau booleen de meme forme que ``V``, typiquement produit par
    :func:`disk_mask` ou :func:`quadrant_mask`). C'est le complement local de
    :func:`structure` : quand on ablate une sous-region du champ (cf
    :func:`ablate`), la variance **globale** bouge a peine (l'ablation d'un
    disque de rayon 8 dans un champ 32x32 ne change que ~8% des cellules) et
    ne capte donc pas la perte de motif. La variance **locale au masque**
    tombe a zero apres ablation (les cellules sont uniformisees a ``V=0``) et
    remonte si la dynamique regenere un motif a cet endroit -- c'est
    l'observable qu'il faut pour mesurer la reparation *in situ* apres une
    intervention ``do(.)`` (Pearl), fil rouge ICT-9 et batterie ENJEU d'ICT-19.

    Retourne ``0.0`` si le masque est vide ou ne selectionne qu'une seule
    cellule (variance non definie).
    """
    V = np.asarray(V, dtype=float)
    mask = np.asarray(mask, dtype=bool)
    vals = V[mask]
    if vals.size < 2:
        return 0.0
    return float(np.var(vals))


def spatial_autocorrelation(field: np.ndarray) -> float:
    """Auto-correlation spatiale au decalage 1 (moyenne des deux axes, bords periodiques).

    Mesure de **l'organisation** spatiale, complementaire de :func:`structure`.
    Pour un champ centre ``f`` ::

        ac = 0.5 * ( <f * roll(f, 1, axe_y)> + <f * roll(f, 1, axe_x)> ) / var(f)

    Vaut ~1 pour un champ lisse et organise (taches de Gray-Scott : les voisins se
    ressemblent), et ~0 pour du bruit blanc (voisins decorreles). C'est exactement
    le discriminant qui manque a la variance seule : un bruit **apparie en variance**
    a une forme reelle a la **meme** :func:`structure` mais une auto-correlation
    quasi nulle. On distingue ainsi « il y a de l'energie » de « il y a une forme ».
    """
    f = np.asarray(field, dtype=float)
    f = f - f.mean()
    var = float(np.mean(f * f))
    if var < 1e-12:
        return 0.0
    ac_y = float(np.mean(f * np.roll(f, 1, axis=0)))
    ac_x = float(np.mean(f * np.roll(f, 1, axis=1)))
    return 0.5 * (ac_y + ac_x) / var


def variance_matched_noise(
    field: np.ndarray, rng: Optional[np.random.Generator] = None
) -> np.ndarray:
    """Champ de **bruit blanc apparie en moyenne et variance** a ``field``.

    Construit un controle adverse pour :func:`structure` : un champ aleatoire sans
    aucune organisation spatiale, mais de **meme moyenne et meme variance** que
    ``field``. Il sert a demontrer que la variance seule ne suffit pas a certifier
    une forme — le bruit apparie obtient le meme score de :func:`structure` tout en
    ayant une :func:`spatial_autocorrelation` quasi nulle.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    f = np.asarray(field, dtype=float)
    target_mean = float(f.mean())
    target_std = float(f.std())
    z = rng.standard_normal(f.shape)
    z = (z - z.mean()) / (z.std() + 1e-12)  # moyenne 0, ecart-type 1 exacts
    return target_mean + target_std * z


def pattern_distance(a: np.ndarray, b: np.ndarray) -> float:
    """Distance morphologique RMS (racine de l'erreur quadratique moyenne).

    ``sqrt(mean((a - b)^2))`` sur les pixels compares. Mesure **stricte et
    locale** (pixel a pixel) : deux motifs de meme texture mais decales spatialement
    en ressortent eloignes. C'est voulu — elle sert de borne pessimiste, a opposer
    a la similarite spectrale (invariante par translation) ci-dessous.
    """
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    return float(np.sqrt(np.mean((a - b) ** 2)))


def _radial_power_spectrum(field: np.ndarray, nbins: int = 24) -> np.ndarray:
    """Spectre de puissance radialement moyenne du champ (invariant par translation).

    On retire la moyenne, on prend ``|FFT2|^2``, on recentre, puis on moyenne la
    puissance par anneaux de frequence radiale. Le resultat decrit la **texture**
    (echelle caracteristique du motif) independamment de la **position** des
    structures — la grandeur pertinente quand un motif se reforme ailleurs.
    """
    f = np.asarray(field, dtype=float)
    f = f - f.mean()
    power = np.abs(np.fft.fftshift(np.fft.fft2(f))) ** 2
    n0, n1 = power.shape
    cy, cx = n0 / 2.0, n1 / 2.0
    yy, xx = np.mgrid[0:n0, 0:n1]
    r = np.sqrt((xx - cx) ** 2 + (yy - cy) ** 2)
    r_max = r.max()
    bins = np.linspace(0.0, r_max + 1e-9, nbins + 1)
    idx = np.digitize(r.ravel(), bins) - 1
    idx = np.clip(idx, 0, nbins - 1)
    spectrum = np.zeros(nbins, dtype=float)
    counts = np.bincount(idx, minlength=nbins).astype(float)
    np.add.at(spectrum, idx, power.ravel())
    counts[counts == 0] = 1.0
    return spectrum / counts


def spectral_similarity(a: np.ndarray, b: np.ndarray, nbins: int = 24) -> float:
    """Similarite cosinus des spectres de puissance radiaux de ``a`` et ``b``.

    Vaut 1 quand les deux champs partagent la **meme texture** (meme echelle
    caracteristique de motif), independamment de la position exacte des structures.
    C'est la mesure **equitable** pour juger d'une regeneration : la reaction-
    diffusion reconstruit des taches de la bonne taille, sans garantir qu'elles
    retombent au pixel pres aux memes endroits.
    """
    sa = _radial_power_spectrum(a, nbins)
    sb = _radial_power_spectrum(b, nbins)
    denom = (np.linalg.norm(sa) * np.linalg.norm(sb)) + 1e-12
    return float(np.dot(sa, sb) / denom)


def energy_gated_spectral_similarity(
    a: np.ndarray,
    b: np.ndarray,
    nbins: int = 24,
    min_variance: float = 1e-4,
) -> float:
    """:func:`spectral_similarity` **protegee par un seuil d'energie**.

    Le cosinus spectral normalise l'amplitude : il peut donc renvoyer une valeur
    elevee en comparant une forme reelle a une zone **sans structure** (un champ
    quasi uniforme dont le spectre, domine par le bruit numerique, s'aligne par
    hasard). C'est la **ressemblance fantome** que le notebook ICT-9 met en garde.

    Cette variante renvoie ``0.0`` des que l'un des deux champs a une variance
    inferieure a ``min_variance`` — autrement dit : *pas d'energie, pas de
    similarite de texture qui vaille*. Le seuil se choisit relativement a la
    variance du substrat structure (typiquement une fraction de la structure de
    reference). Au-dessus du seuil, le comportement est identique a
    :func:`spectral_similarity`.
    """
    if min(float(np.var(a)), float(np.var(b))) < min_variance:
        return 0.0
    return spectral_similarity(a, b, nbins)


# --------------------------------------------------------------------------- #
# Scores de recuperation et d'agence
# --------------------------------------------------------------------------- #


def recovery_score(
    reference: np.ndarray,
    ablated: np.ndarray,
    repaired: np.ndarray,
    mask: Optional[np.ndarray] = None,
) -> float:
    """Fraction de structure restauree dans la region endommagee.

    Compare la **variance** (cf. :func:`structure`) du champ dans la region ``mask``
    a trois instants : ``reference`` (avant ablation), ``ablated`` (juste apres
    l'ablation, structure quasi nulle), ``repaired`` (apres laisse-evoluer) ::

        recovery = (S_repaired - S_ablated) / (S_reference - S_ablated)

    Vaut ~1 si la structure de la region est integralement reconstituee, ~0 si
    rien ne repousse, et peut depasser 1 en cas de sur-reconstruction. Robuste a
    la position exacte des taches (mesure d'amplitude, pas pixel a pixel).
    """
    sel = (lambda x: x[mask]) if mask is not None else (lambda x: x)
    s_ref = float(np.var(sel(reference)))
    s_abl = float(np.var(sel(ablated)))
    s_rep = float(np.var(sel(repaired)))
    denom = s_ref - s_abl
    if abs(denom) < 1e-12:
        return 0.0
    return (s_rep - s_abl) / denom


def repair_gain(recovery_reaction_diffusion: float, recovery_diffusion: float) -> float:
    """Gain de reparation = recuperation (reaction-diffusion) - recuperation (diffusion).

    **C'est la mesure d'agence du notebook.** Strictement positif et substantiel,
    il signe une trajectoire qui *repare activement* ; proche de zero ou negatif,
    il signe une evolution passive. Le contraste do-calculus est ici explicite :
    meme ``do(ablation)``, deux mondes, une difference.
    """
    return float(recovery_reaction_diffusion - recovery_diffusion)


def time_to_recover(
    structures: List[float],
    target: float,
    tol: float = 0.1,
    record_every: int = 1,
) -> Optional[int]:
    """Premier instant (en pas) ou la structure repasse au-dessus de ``target * (1 - tol)``.

    ``structures`` est la trajectoire de :func:`structure` capturee tous les
    ``record_every`` pas. Retourne le nombre de pas ecoules, ou ``None`` si le
    seuil n'est jamais atteint (la forme ne se reconstruit pas).
    """
    threshold = target * (1.0 - tol)
    for i, s in enumerate(structures):
        if s >= threshold:
            return i * record_every
    return None


def basin_return_probability(
    model,
    U_ref: np.ndarray,
    V_ref: np.ndarray,
    make_mask: Callable[[np.random.Generator], np.ndarray],
    steps: int,
    target_structure: float,
    tol: float = 0.2,
    n_trials: int = 5,
    rng: Optional[np.random.Generator] = None,
) -> float:
    """Probabilite de **retour au bassin** apres une ablation aleatoire.

    Sur ``n_trials`` essais : on ablate une region tiree par ``make_mask`` puis on
    laisse le ``model`` (un :class:`ict.reaction_diffusion.GrayScott`) integrer
    ``steps`` pas ; on compte un succes si la structure finale revient a
    ``target_structure`` a ``tol`` pres. Retourne la fraction de succes.

    AVERTISSEMENT (honnetete) : cette mesure est **stochastique et couteuse** —
    chaque essai est une simulation complete. Avec peu d'essais, l'estimation a
    une forte variance ; l'augmenter exige du temps de calcul. Le notebook
    l'utilise avec un ``n_trials`` modeste et le **documente comme tel**, sans
    sur-interpreter une statistique a petit echantillon.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    successes = 0
    lo = target_structure * (1.0 - tol)
    hi = target_structure * (1.0 + tol)
    for _ in range(n_trials):
        mask = make_mask(rng)
        U0, V0 = ablate(U_ref, V_ref, mask)
        _, V_end, _ = model.run(U0, V0, steps)
        s = structure(V_end)
        if lo <= s <= hi:
            successes += 1
    return successes / float(n_trials)
