"""Cognition analogique par ondes cerebrales : monde jouet numpy (ICT-40).

Operationnalisation des mecanismes du preprint Earl K. Miller, Scott L.
Brincat & Jefferson E. Roy, « Analog Cognition and Consciousness »
(PsyArXiv z48x7_v3, 2026-07-07) — la these hybride spikes/ondes : les
synapses stockent l'information, les champs electriques rythmiques (ondes
cerebrales) exercent un controle top-down mesoscopique via couplage
ephaptique, et la superposition des ondes effectue du calcul analogique.

Quatre mecanismes, quatre bancs toyet deterministes :

1. **Gating ephaptique par phase** — des neurones proches du seuil de spike
   voient leur probabilite de tir modulee par la phase du champ local
   (``spike_phase_tuning``). C'est le « radar d'excitabilite » de Davis et
   al. 2020, en jouet.

2. **Spatial Computing** (Lundqvist et al. 2023) — un stencil inhibiteur
   alpha/beta spatial module ou le contenu feedforward (objets) s'exprime
   (``object_weight_maps``, ``express``, ``stencil_from_wave``). Deux
   stencils = deux contextes ; la meme connectivite chevauchante produit
   alors une **selectivite mixte emergente** (``mixed_selectivity_index``).

3. **Calcul analogique par interference** (Fig. 6-7 du preprint) — deux
   ondes de contexte se somment ; la somme contraint l'activite a un
   patron unique par combinaison de contextes, sans recablage
   (``wave_field``, ``combine``, ``pattern_distance_matrix``).

4. **Onde voyageuse et transition de sous-espace** — un front qui balaie
   la feuille corticale interpole le stencil d'un patron (encodage
   sensoriel) vers un autre (memoire de travail) ; la trajectoire
   populationnelle passe d'un sous-espace a l'autre, mesure par l'angle
   principal (``traveling_stencil``, ``principal_angle``).

5. **Anesthesie et desorganisation** — le regime organisé (gradient de
   phase coherent) vs le regime anesthesique (lent, desaligne) : la valeur
   de verrouillage de phase inter-regionale s'effondre (``regional_fields``,
   ``phase_locking_value``), proxy d'integration a grande echelle.

Garde-fous (repetes dans le notebook ICT-40) : monde jouet idealise !=
cerveau ; les mesures valident des MECANISMES (gating par phase,
intersection de contraintes par superposition, transition de sous-espace,
effondrement de coherence), pas la theorie de la conscience ; le preprint
n'est pas relu. Le pont vers Phi (ICT-15) passe par des proxies grossiers
de coherence, jamais par un calcul IIT strict.

Hors numpy/scipy, aucune dependance. Toutes les fonctions acceptent une
graine : determinisme complet.
"""

from __future__ import annotations

import numpy as np
from scipy.ndimage import gaussian_filter
from scipy.signal import hilbert

__all__ = [
    "make_grid",
    "spike_phase_tuning",
    "modulation_depth",
    "stencil_from_wave",
    "object_weight_maps",
    "express",
    "mixed_selectivity_index",
    "wave_field",
    "combine",
    "sum_amplitude_vs_phase",
    "pattern_distance_matrix",
    "traveling_stencil",
    "principal_angle",
    "regional_fields",
    "phase_locking_value",
]


# ---------------------------------------------------------------------------
# 1. Gating ephaptique par phase
# ---------------------------------------------------------------------------

def spike_phase_tuning(
    field_amp: float,
    margin: float = 0.15,
    sigma: float = 0.25,
    n_bins: int = 36,
    n_trials: int = 40_000,
    seed: int = 0,
) -> tuple[np.ndarray, np.ndarray]:
    """Probabilite de spike par phase de champ, pour un neurone au seuil.

    Le potentiel membranaire au repos fluctue autour du seuil (``margin``
    en unites de sigma) ; le champ ephaptique ajoute ``field_amp * cos(phi)``.
    La probabilite de spike par fenetre temporelle suit une sigmoide au
    seuil. Retourne (centres de bins en radians, taux empirique par bin).

    Le papier (§ « Brain waves directly influence activity via ephaptic
    coupling ») : memes synapses bloquees, le champ seul module le tir.
    """
    rng = np.random.default_rng(seed)
    phases = rng.uniform(0.0, 2.0 * np.pi, size=n_trials)
    v = margin + field_amp * np.cos(phases)
    p = 1.0 / (1.0 + np.exp(-v / sigma))
    spikes = rng.random(n_trials) < p
    edges = np.linspace(0.0, 2.0 * np.pi, n_bins + 1)
    idx = np.clip(np.digitize(phases, edges) - 1, 0, n_bins - 1)
    rate = np.array([spikes[idx == b].mean() for b in range(n_bins)])
    centers = 0.5 * (edges[:-1] + edges[1:])
    return centers, rate


def modulation_depth(rate: np.ndarray) -> float:
    """Ecart max-min du taux de spike : profondeur de modulation du gating."""
    return float(rate.max() - rate.min())


# ---------------------------------------------------------------------------
# 2. Spatial Computing : stencil inhibiteur et activite exprimee
# ---------------------------------------------------------------------------

def make_grid(h: int = 48, w: int = 96) -> tuple[np.ndarray, np.ndarray]:
    """Coordonnees normalisees x, y dans [0, 1] d'une feuille corticale."""
    y, x = np.mgrid[0:h, 0:w]
    return x / (w - 1), y / (h - 1)


def stencil_from_wave(
    x: np.ndarray,
    y: np.ndarray,
    angle: float,
    phase: float,
    k: float = 2.0 * np.pi,
) -> np.ndarray:
    """Stencil inhibiteur alpha/beta : demi-onde positive, dans [0, 1].

    1 = suppression forte (phase excitatrice du rythme de controle ailleurs
    traduite en inhibition locale du gamma/spiking, cf. push-pull
    alpha/beta vs gamma), 0 = region « ouverte » ou le feedforward
    s'exprime librement.
    """
    proj = x * np.cos(angle) + y * np.sin(angle)
    return np.clip(np.cos(k * proj + phase), 0.0, 1.0)


def object_weight_maps(
    h: int = 48,
    w: int = 96,
    n_objects: int = 2,
    corr_len: float = 6.0,
    seed: int = 1,
) -> np.ndarray:
    """Cartes de poids synaptiques spatiaux par objet, chevauchantes.

    Bruit gaussien lisse normalise : chaque voxel recoit des connexions
    pour plusieurs objets (connectivite chevauchante, precondition de la
    selectivite mixte). Forme (n_objects, h, w), valeurs dans [0, 1].
    """
    rng = np.random.default_rng(seed)
    maps = np.stack(
        [gaussian_filter(rng.normal(size=(h, w)), corr_len) for _ in range(n_objects)]
    )
    maps = np.clip(maps, 0.0, None)
    maps /= maps.max()
    return maps


def express(
    weights: np.ndarray,
    objects: np.ndarray,
    stencil: np.ndarray,
    noise: float = 0.02,
    seed: int = 2,
) -> np.ndarray:
    """Activite exprimee : drive synaptique sculpte par le stencil inhibiteur.

    rate = (somme des poids ponderes par la presence des objets) * (1 - stencil)
    + bruit de spike. Le contenu est dans la connectivite, l'expression est
    decidee par le stencil — la separation control/contenu du Spatial
    Computing (Fig. 3 du preprint).
    """
    drive = np.tensordot(objects, weights, axes=1)
    rng = np.random.default_rng(seed)
    rate = drive * (1.0 - stencil) + rng.normal(size=drive.shape) * noise
    return np.clip(rate, 0.0, None)


def mixed_selectivity_index(resp: np.ndarray) -> float:
    """Fraction de voxels dont la preference d'objet change entre contextes.

    ``resp`` : (n_ctx, n_obj, h, w). Un voxel « pur » garde la meme
    preference d'objet quel que soit le contexte ; un voxel a selectivite
    mixte la change (Warden & Miller 2007, Rigotti et al. 2013). L'indice
    mesure l'emergence de la mixite SOUS stencil, sachant que les poids
    sont fixes.
    """
    prefs = np.argmax(resp, axis=1)  # (n_ctx, h, w)
    return float((prefs[0] != prefs[1]).mean())


# ---------------------------------------------------------------------------
# 3. Calcul analogique : superposition et intersection de contraintes
# ---------------------------------------------------------------------------

def wave_field(
    x: np.ndarray, y: np.ndarray, angle: float, phase: float, k: float = 4.0 * np.pi
) -> np.ndarray:
    """Onde plane cosinus sur la feuille : le signal de controle brut."""
    proj = x * np.cos(angle) + y * np.sin(angle)
    return np.cos(k * proj + phase)


def combine(*waves: np.ndarray) -> np.ndarray:
    """Somme des ondes : l'interaction EST le calcul (preprint Fig. 6-7)."""
    return np.sum(np.stack(waves), axis=0)


def sum_amplitude_vs_phase(delta_phi: float, k: float = 2.0 * np.pi) -> float:
    """Amplitude exacte de la somme de deux ondes 1D dephasées de delta_phi.

    Identite analytique 2*|cos(delta_phi/2)| — le temoin exact que la
    superposition code bien l'interaction des variables continues.
    """
    return float(2.0 * abs(np.cos(delta_phi / 2.0)))


def pattern_distance_matrix(patterns: np.ndarray) -> np.ndarray:
    """Matrice des distances cosinus entre patrons applatis (n, n).

    Un bloc anti-diagonal charge = des patrons bien distingues ; des
    lignes quasi nulles = des combinaisons de contextes confondues.
    """
    flat = patterns.reshape(len(patterns), -1)
    norms = np.linalg.norm(flat, axis=1, keepdims=True)
    unit = flat / np.maximum(norms, 1e-12)
    sim = unit @ unit.T
    return 1.0 - sim


# ---------------------------------------------------------------------------
# 4. Onde voyageuse : transition entre sous-espaces de codage
# ---------------------------------------------------------------------------

def traveling_stencil(
    x: np.ndarray,
    y: np.ndarray,
    t: float,
    direction: float = 0.0,
    speed: float = 0.9,
    width: float = 0.06,
    pattern_from: np.ndarray | None = None,
    pattern_to: np.ndarray | None = None,
) -> np.ndarray:
    """Stencil interpole par un front voyageur de pattern_from vers pattern_to.

    Le front (tangente hyperbolique sur la projection le long de
    ``direction``) balaie la feuille a vitesse ``speed`` : derriere lui le
    nouveau stencil, devant lui l'ancien. « Spatial Computing in motion »
    (preprint, Fig. 5) : l'onde voyageuse INSTANTIE la transition entre
    sous-espaces de codage (sensoriel -> memoire de travail).
    """
    if pattern_from is None or pattern_to is None:
        raise ValueError("fournir pattern_from et pattern_to")
    proj = x * np.cos(direction) + y * np.sin(direction)
    front = t * speed - 0.3
    # region balayee = proj < front : le front part a gauche de la feuille
    # (gate=0 -> pattern_from) et la traverse au fil de t (gate=1 -> pattern_to)
    gate = 0.5 * (1.0 + np.tanh((front - proj) / width))
    return pattern_from * (1.0 - gate) + pattern_to * gate


def principal_angle(a: np.ndarray, b: np.ndarray, dim: int = 2) -> float:
    """Angle principal (degres) entre les sous-espaces de deux nuages (T, D).

    0 deg = memes directions de variance (meme sous-espace de codage) ;
    90 deg = sous-espaces orthogonaux. Mesure la separation des
    sous-espaces de contexte (preprint, « subspace coding »).
    """
    def subspace(m: np.ndarray) -> np.ndarray:
        centered = m - m.mean(axis=0)
        _, _, vt = np.linalg.svd(centered, full_matrices=False)
        return vt[:dim]

    # svd croise des directions principales (dim, D) : les singulieres sont
    # les cosinus des angles principaux — insensible a des longueurs T
    # differentes entre les deux nuages.
    s = np.linalg.svd(subspace(a) @ subspace(b).T, compute_uv=False)
    return float(np.degrees(np.arccos(np.clip(s.min(), 0.0, 1.0))))


# ---------------------------------------------------------------------------
# 5. Anesthesie : coherence inter-regionale organisee vs desorganisee
# ---------------------------------------------------------------------------

def regional_fields(
    n_regions: int = 12,
    n_t: int = 2000,
    freq: float = 10.0,
    phase_offsets: np.ndarray | None = None,
    amplitude: float = 1.0,
    jitter: float = 0.0,
    seed: int = 3,
    fs: float = 200.0,
) -> np.ndarray:
    """Champs regionaux : oscillations avec phases imposees + gigue.

    Regime organise : offsets en gradient lisse (ondes voyageantes
    coherentes, frequence alpha/beta). Regime anesthesique : offsets
    aleatoires, frequence delta lente, forte gigue (Bardon et al. 2025,
    Eisen et al. 2026 — la convergence des anesthesiques vers des ondes
    lentes desalignees). Forme (n_regions, n_t).
    """
    rng = np.random.default_rng(seed)
    if phase_offsets is None:
        phase_offsets = np.zeros(n_regions)
    t = np.arange(n_t) / fs
    walk = np.cumsum(rng.normal(0.0, jitter, size=(n_regions, n_t)), axis=1)
    fields = np.stack(
        [
            amplitude * np.sin(2.0 * np.pi * freq * t + phase_offsets[r] + walk[r])
            for r in range(n_regions)
        ]
    )
    return fields + rng.normal(0.0, 0.05, size=fields.shape)


def phase_locking_value(fields: np.ndarray, skip: int = 500) -> float:
    """PLV moyenne sur paires de regions, sur la portion stationnaire.

    |mean(exp(i(phi_r - phi_s)))| via signal analytique de Hilbert : 1 =
    phases verrouillees (integration a grande echelle), ~0 = independance.
    Proxy grossier de l'integration mesoscopique — PAS un Phi IIT.
    """
    sig = fields[:, skip:]
    analytic = hilbert(sig, axis=1)
    phase = np.angle(analytic)
    n = phase.shape[0]
    plvs = []
    for i in range(n):
        for j in range(i + 1, n):
            plv = np.abs(np.mean(np.exp(1j * (phase[i] - phase[j]))))
            plvs.append(plv)
    return float(np.mean(plvs))
