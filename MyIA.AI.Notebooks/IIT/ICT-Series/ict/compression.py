"""La jambe compression (K) du capstone ICT-15 (strate 4, Epic #4588, See #5090).

La theorie fondatrice (*Integrated Complexity Theory*, cadrage verbatim dans
ICT-0) pose que l'integration (Φ), la surprise (F) et la **compression** (K)
sont trois facettes d'un meme quantite : *un systeme qui modelise son monde*.
ICT-14 a attache la jambe energie-libre au representant interne ``p_hat`` ; ce
module attache la jambe compression a la **trajectoire**.

K est mesure par la **longueur zlib** (niveau 9) de la sequence serialisee
canoniquement : les labels sont re-indexes par ordre de premiere apparition en
entiers, ce qui rend la mesure reproductible et independante du choix de
labels. Le gain ``k_gain`` contraste la longueur reelle a celle d'une
trajectoire permutee (le meme multi-ensemble d'etats, structure temporelle
detruite). Comme le shuffle preserve exactement les **frequences** d'etats, la
compression d'ordre 0 (Huffman-like) est identique des deux cotes : tout gain
zlib attribuable est donc de la **structure d'ordre** (les regularites de
transitions), pas du reservoir d'etats. L'overhead d'en-tete zlib (fixed
dictionnaire + framing) s'annule dans le contraste.

La courbe de Schmidhuber (``compression_progress``) trace la **compressibilite
de l'histoire accumulee** : au fur et a mesure que le systeme decouvre une
structure, son passe se compresse mieux. C'est la signature temporelle de
l'apprentissage/compression, au meme titre que le ralentissement critique
(ICT-8) ou le pic de surprise (ICT-14 Gate 3) sont des signatures temporelles
de la bifurcation.

Sans complaisance : la compression zlib est un estimateur BRUT de K (le MDL
optimal exigerait un modele explicite, cf. ICT-16). Mais c'est un estimateur
**honnete** : (1) sans parametre libre, (2) le contraste shuffle isole la
structure d'ordre, (3) toute amelioration par un meilleur compresseur (LZMA,
exercice C du notebook) ne peut que rapprocher K de la vraie complexite de
Kolmogorov -- le verdict Gate 4 (convergence Φ/F/K) est teste pour sa robustesse
au compresseur dans le notebook.

Dependances : bibliotheque standard (``zlib``) + numpy. Aucune dependance au
package ``ict`` -- ce module est volontairement autonome, comme
``causal_emergence``.
"""

from __future__ import annotations

import zlib
from typing import List, Sequence

import numpy as np


def canonical_int_sequence(states: Sequence) -> List[int]:
    """Re-indexe les labels d'une trajectoire en entiers consecutifs.

    L'attribution suit l'ordre de PREMIERE apparition (comme
    ``tpm_estimation.state_index_map``), ce qui rend la serialisation
    reproductible et independante du choix de labels. Les labels non hachables
    ou les types mixtes sont supportes tant qu'ils sont comparables pour
    l'egalite.
    """
    mapping: dict = {}
    out: List[int] = []
    for s in states:
        if s not in mapping:
            mapping[s] = len(mapping)
        out.append(mapping[s])
    return out


def compressed_length(states: Sequence, level: int = 9) -> int:
    """Longueur (octets) de la sequence canonique compressee par zlib.

    La sequence est serialisee en octets canoniques (un octet par etat indexe,
    ou la forme packed varint si >256 etats), puis compressee au ``level``
    demande (defaut 9, maximum). Retourne le nombre d'octets de la sortie
    compresse -- la mesure operationnelle de K.

    Le niveau est fixe (9) pour la reproductibilite ; le contraste shuffle
    annule l'overhead constant de framing.
    """
    seq = canonical_int_sequence(states)
    if not seq:
        return 0
    maxv = max(seq)
    if maxv < 256:
        payload = bytes(seq)
    else:
        # Packing varint simple : un octet de continuation (MSB) par digit base-128.
        buf = bytearray()
        for v in seq:
            while True:
                b = v & 0x7F
                v >>= 7
                if v:
                    buf.append(b | 0x80)
                else:
                    buf.append(b)
                    break
        payload = bytes(buf)
    return len(zlib.compress(payload, level))


def compression_gain(states: Sequence, rng: np.random.Generator,
                     n_shuffles: int = 20, level: int = 9) -> dict:
    """Gain de compression : reel vs controle permute (le signal credite).

    ``k_gain = (len_shuffle - len_real) / len_shuffle`` : fraction de la
    longueur compresse qui est epargnee par la structure d'ordre reelle. Positif
    quand la trajectoire reelle est plus compressible qu'une permutation de
    memes etats (signe de regularite temporelle) ; ~0 si la dynamique est
    essentiellement permutatoire.

    Retourne ``len_real``, ``len_shuffled`` (moyenne), ``k_gain`` et
    ``n_shuffles``. La dispersion est negligee : l'overhead zlib domine aux
    courtes longueurs, rendant l'ecart-type peu informatif -- le contraste de
    moyenne suffit au gate.
    """
    real = compressed_length(states, level=level)
    seq = list(states)
    lens = []
    for _ in range(int(n_shuffles)):
        idx = rng.permutation(len(seq))
        perm = [seq[i] for i in idx]
        lens.append(compressed_length(perm, level=level))
    shuffled = float(np.mean(lens)) if lens else float(real)
    denom = shuffled if shuffled > 0 else 1.0
    return {
        "len_real": int(real),
        "len_shuffled": float(shuffled),
        "k_gain": float((shuffled - real) / denom),
        "n_shuffles": int(n_shuffles),
    }


def compression_progress(states: Sequence, window: int,
                         level: int = 9) -> dict:
    """Courbe de Schmidhuber : compressibilite de l'histoire accumulee.

    Pour chaque pas ``t`` (de ``window`` a ``len(states)``), calcule la longueur
    compresse du prefixe ``states[:t]`` rapportee au prefixe ``states[:t-window]``
    : la **derivee de la compressibilite de l'histoire**. Quand le systeme
    decouvre une structure (un attracteur, un cycle, une regle), son passe
    recent ajoute peu d'information nouvelle -> le ratio chute. Quand il explore
    de la nouveauté, le ratio grimpe.

    ``window`` : taille du pas de differentiation (trop petit = bruit de
    quantification zlib ; trop grand = moyenne trop lisse). Retourne ``steps``
    (les ``t``) et ``ratio`` (longueur[t] / longueur[t-window]).
    """
    seq = list(states)
    if window < 1:
        raise ValueError(f"window doit etre >= 1, recu {window}")
    steps: List[int] = []
    ratios: List[float] = []
    prev_len = compressed_length(seq[:window], level=level)
    for t in range(window, len(seq) + 1):
        cur = compressed_length(seq[:t], level=level)
        denom = prev_len if prev_len > 0 else 1.0
        steps.append(t)
        ratios.append(float(cur / denom))
        prev_len = cur
    return {"steps": np.asarray(steps), "ratio": np.asarray(ratios),
            "window": int(window)}
