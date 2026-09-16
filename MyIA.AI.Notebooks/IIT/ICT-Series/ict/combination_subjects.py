"""Jouet « combinaison des sujets » pour la distillation du combination problem (case 13, #8182 iceberg L2 — panpsychisme, non-marqué).

Le combination problem en une phrase : si chaque micro-entité porte une
propriété mentale (proto-phénoménale), comment la COMPOSITION de ces
micro-propriétés rend-elle intelligible la macro-propriété — le sujet
composé ? Nommé par Seager (1995), forme acérée par Goff ; l'entrée
SEP (Goff, Seager & Allen-Hermanson, rév. 2022-05-13) exige que la
combinaison soit « transparente a priori » — sans apparatus
quantitatif (vérifié firsthand 2026-09-14 : aucune équation chez la
source). La lecture critique (« subject-summing ») : la composition
n'est qu'AGRÉGATION, et agréger des sujets n'a jamais fait un sujet.
Ce module rend la question falsifiable AU NIVEAU SIGNAL (grade C
documentaire — aucune phénoménologie n'est mesurée ni revendiquée).

Construction v2 (pavages tournés) — l'instrument v1 (anneau D=8,
stride t) a été invalide par son PROPRE contrôle mécanique : le
« ρ=0 » attendu à gap nul exact a mesuré −0.345, cause racine =
l'enroulement (3 ne divisant pas 8, aucune tuile contiguë disjointe
n'existe — chaque coordonnée était relue 3 fois ; en plus
round(κ·8) confondait κ=0.2 et κ=0.3). La v2 reconstruit les fenêtres
en m PAVAGES TOURNÉS : D multiple de k, fenêtres contiguës de k
coordonnées, le pavage r étant décalé de r. Chaque coordonnée est lue
par EXACTEMENT m unités (multiplicité uniforme, assert en
construction), le bras m=1 est disjoint PAR CONSTRUCTION, et le
chevauchement est rho = (m-1)/m. Les fractions de corrompus
RÉALISÉES (round(kappa·N)) sont rapportées dans chaque mesure.

Deux enseignements MÉCANIQUES (démontrables sans exécution) :
- m=1 : lecture unique — les deux estimateurs calculent la même
  fonction sur la même lecture -> gap = 0 exact, pour tout kappa.
- m=2 : l'unanimité-2 est un transform monotone de la somme-2 par
  coordonnée (n_pos ∈ {0,1,2} donne le même signe aux deux
  estimateurs) -> gap = 0 exact, pour tout kappa. La COMBINAISON
  NON-TRIVIALE n'existe pas sous trois lecteurs par coordonnée
  partagée : deux sujets qui partagent une coordonnée font encore du
  recensement, pas une composition.

Dérivation corrigée (l'erreur de la v1, identifiée en réparant
l'instrument) : la v1 dérivait son crossover de P(Binom(m, kappa)≥2)
— majorités d'UNITÉS corrompues — en les traitant comme majorités de
LECTURES fausses. Une unité corrompue lit faux avec probabilité
1-alpha seulement : l'erreur par lecture est p̄ = (1-alpha) +
kappa(2alpha-1), et la majorité des lectures d'une coordonnée garde
le signe correct TANT QUE p̄ < 1/2, i.e. kappa < 1/2. Le crossover
vit donc de l'autre côté du seuil : sous attaque MINORITAIRE
(kappa < 1/2) l'agrégat n'est jamais empoisonné et le lien ne fait
que coûter (gap < 0) ; sous attaque MAJORITAIRE (kappa > 1/2)
l'agrégat tombe sous le hasard tandis que le rejet-de-discorde
retombe au seuil 1/2 (gap > 0). **Le bond ne paie que dans les mondes
où la majorité des micro-sujets mentent.**

Anti-confusion vs ICT-15d : 15d teste l'OBSTRUCTION au recollement des
proxys (existence du glue sur des substrats corpus) ; la case 13 teste
le TRANSFERT DE PROPRIÉTÉ par la composition (le glue comme variable
manipulée, substrat jouet markovien) — observable et substrat
distincts, falsifiable indépendamment.

References
----------
Philip Goff, William Seager & Sean Allen-Hermanson, « Panpsychism »,
Stanford Encyclopedia of Philosophy, substantive revision 2022-05-13,
https://plato.stanford.edu/entries/panpsychism/. Problème nommé par
William Seager (1995) ; formulation acérée par Philip Goff (2006+) ;
précédents historiques Lucretius / Samuel Clarke (notes SEP). Vérifié
firsthand 2026-09-14.
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "MicroUnits",
    "aggregate_map",
    "glued_map",
    "combination_gap",
]

# Paramètres de la construction (verrouillés avant exécution, case 13 v2).
D_COORDS = 12      # état global W : 12 bits (multiple de k ; CTRL : 24)
K_WINDOW = 3       # chaque unité lit 3 coordonnées consécutives
ALPHA = 0.8        # fidélité du canal micro (P(bit correct))
# m ∈ {1, 2, 3} pavages tournés -> rho = (m-1)/m ∈ {0, 1/2, 2/3}


def _log_ratio(alpha: float) -> float:
    """Log-vraisemblance unitaire d'un bit correct (base 2, symétrique)."""
    return float(np.log2(alpha / (1.0 - alpha)))


class MicroUnits:
    """N = m·(D/k) unités en m pavages tournés ; multiplicité m uniforme.

    Parameters
    ----------
    overlap_m :
        nombre de pavages = multiplicité de lecture par coordonnée ;
        ``rho = (m - 1) / m`` ; m=1 -> pavage disjoint (une lecture par
        coordonnée, les deux estimateurs y coïncident mécaniquement).
    alpha :
        fidélité du canal d'une unité saine.
    kappa :
        fraction d'unités corrompues (canal inversé, fidélité ``1 - alpha``).
    seed :
        graine RNG (canal + tirage des corrompues).
    d_coords :
        nombre de coordonnées de W (multiple de ``K_WINDOW``).
    """

    def __init__(self, overlap_m: int, alpha: float, kappa: float, seed: int,
                 d_coords: int = D_COORDS) -> None:
        if d_coords % K_WINDOW != 0:
            raise ValueError("d_coords doit etre multiple de K_WINDOW")
        self.d = d_coords
        self.m = overlap_m
        self.alpha = alpha
        self.kappa = kappa
        self.rng = np.random.default_rng(seed)
        self.windows = []
        for r in range(overlap_m):
            for j in range(d_coords // K_WINDOW):
                start = (K_WINDOW * j + r) % d_coords
                self.windows.append(tuple((start + t) % d_coords
                                          for t in range(K_WINDOW)))
        self.n = len(self.windows)
        # coordonnées vues par chaque unité -> unités voyant chaque coordonnée
        self.readers: list[list[int]] = [[] for _ in range(d_coords)]
        for i, w in enumerate(self.windows):
            for c in w:
                self.readers[c].append(i)
        if any(len(r) != overlap_m for r in self.readers):
            raise ValueError("multiplicite non uniforme : construction cassee")
        n_corrupt = int(round(kappa * self.n))
        idx = self.rng.permutation(self.n)[:n_corrupt]
        self.corrupt = np.zeros(self.n, dtype=bool)
        self.corrupt[idx] = True

    @property
    def rho(self) -> float:
        """Fraction d'une fenêtre co-lue par d'autres unités : (m-1)/m."""
        return (self.m - 1) / self.m

    def read(self, w_state: np.ndarray) -> np.ndarray:
        """Lectures binaires (n_units, k) : bits de la fenêtre passés au canal."""
        n_reads = np.empty((self.n, K_WINDOW), dtype=np.int8)
        for i, win in enumerate(self.windows):
            bits = w_state[list(win)]
            fid = (1.0 - self.alpha) if self.corrupt[i] else self.alpha
            flip = self.rng.random(K_WINDOW) > fid
            n_reads[i] = np.where(flip, 1 - bits, bits)
        return n_reads


def aggregate_map(mu: MicroUnits, reads: np.ndarray) -> np.ndarray:
    """MAP agrégé : produit de toutes les lectures (comptage multiple).

    Retourne Ŵ (D bits). Chaque lecture vote avec sa vraisemblance de
    canal (saine : alpha ; corrompue : 1-alpha — inconnue du MAP, qui
    traite toutes les unités comme saines : c'est la lecture critique,
    « juste additionner »).
    """
    lr = _log_ratio(mu.alpha)
    scores = np.zeros(mu.d)
    for i, win in enumerate(mu.windows):
        for j, c in enumerate(win):
            bit = int(reads[i, j])
            # P(bit | coord=v) pour v in {0,1} en log : +lr si v=bit, -lr sinon
            scores[c] += lr if bit == 1 else -lr
    return (scores > 0).astype(np.int8)


def glued_map(mu: MicroUnits, reads: np.ndarray) -> np.ndarray:
    """MAP structuré : par coordonnée, unanimité -> une contribution ; discorde -> uniforme."""
    lr = _log_ratio(mu.alpha)
    scores = np.zeros(mu.d)
    for c in range(mu.d):
        units = mu.readers[c]
        if not units:
            continue
        pos = [i for i in units if reads[i, mu.windows[i].index(c)] == 1]
        n_seen = len(units)
        if len(pos) == n_seen:            # unanimité 1
            scores[c] += lr
        elif len(pos) == 0:               # unanimité 0
            scores[c] -= lr
        # divergence -> contribution uniforme (score 0) : la discorde EXCLUT
    return (scores > 0).astype(np.int8)


def combination_gap(mu: MicroUnits, n_states: int, seed: int) -> dict:
    """Écart de précision (glué − agrégé) sur ``n_states`` états globaux.

    Deux observables : appariement exact (``gap``, plancher ~2^-D —
    secondaire) et précision PAR COORDONNÉE (``gap_bit``, primaire :
    résout la structure de signe là où l'appariement exact sature).
    """
    rng = np.random.default_rng(seed)
    acc_a = acc_g = 0
    bit_a = bit_g = 0
    total_bits = 0
    for _ in range(n_states):
        w = rng.integers(0, 2, size=mu.d).astype(np.int8)
        reads = mu.read(w)
        wa = aggregate_map(mu, reads)
        wg = glued_map(mu, reads)
        acc_a += int(np.array_equal(wa, w))
        acc_g += int(np.array_equal(wg, w))
        bit_a += int((wa == w).sum())
        bit_g += int((wg == w).sum())
        total_bits += mu.d
    return {
        "acc_aggregate": acc_a / n_states,
        "acc_glued": acc_g / n_states,
        "gap": (acc_g - acc_a) / n_states,
        "acc_aggregate_bit": bit_a / total_bits,
        "acc_glued_bit": bit_g / total_bits,
        "gap_bit": (bit_g - bit_a) / total_bits,
        "rho": mu.rho,
        "kappa_nominal": mu.kappa,
        "kappa_realized": float(mu.corrupt.sum()) / mu.n,
        "n_units": mu.n,
        "m": mu.m,
        "d": mu.d,
    }
