"""Assemblage du triplet (sigma, K, ordre) d'un debat argumentatif.

Palier 21 « Argumentation et croyances » (capstone strate 6, #23777). La
note de conception (``docs/ict/palier21-argumentation-note-de-conception.md``,
PR #23786) tranche a sa section 3, question 3 : une fonction d'interface
rend, pour une trajectoire de croyance donnee, les trois lectures du gate
re-decoupe (§5.3 de la note) en un appel -- sinon trois imports et trois
formats de retour dans le carnet, donc trois occasions de divergence.

Les trois jambes sont rendues **cote a cote, sans agregation scalaire**
(le gate est un triplet, pas une note) :

  - ``sigma`` (irreversibilite) : ``argumentation.discourse_irreversibility``
    sur la TPM estimee du debat -- l'organe embarque deja
    ``time_arrow.entropy_production`` (production d'entropie) et la distance
    a la projection reversible ;
  - ``K`` (compressibilite) : ``mdl.tpm_description_length`` sur les comptes
    de transitions, plus ``compression.compressed_length`` sur la sequence
    d'etats canonique ;
  - ``ordre`` (ordre causal) : ``mdl.fit_markov_order`` a ordre de Markov
    croissant, plus les contre-factuels permutes de #7742 tranche 1 --
    le sigma de l'ordre du recit confronte aux sigma d'ordres d'arrivee
    permutes, tires avec une graine explicite.

Aucun organe n'est reimplemente : la TPM vient de
``tpm_estimation.tpm_from_trajectory`` (l'appel exact que fait
``argumentation.belief_transition_matrix``), et les mesures des modules
``argumentation``, ``mdl`` et ``compression`` sont invoquees telles quelles.
Un :class:`~ict.argumentation.RefusDeMesure` leve par un organe traverse sans
etre converti en nombre : un refus n'est pas un zero.

Position dans la strate 6 : la jambe sigma est rapportee **non discriminante
a la taille disponible** par la note (§5.3) ; l'assemblage la rend quand
meme, parce qu'un null non mesure ne peut pas etre compare aux
contre-factuels permutes -- c'est le role de la jambe ``ordre`` de le faire
parler.
"""

from __future__ import annotations

from typing import Dict, List, Sequence, Tuple

import numpy as np

from . import argumentation
from . import compression
from . import mdl
from . import tpm_estimation
from .argumentation import DungAF, RefusDeMesure

__all__ = ["assembler_triplet"]


# --------------------------------------------------------------------------- #
#  Encodage des etats (meme pipeline que belief_transition_matrix)             #
# --------------------------------------------------------------------------- #


def _encoder_etats(
    af: DungAF,
    order: Sequence[int],
    encoding: str,
) -> List[Tuple]:
    """Trajectoire de croyance encodee en etats, comme ``belief_transition_matrix``.

    Le prefixe d'etat vide (``include_empty=True``) est conservé : c'est lui
    qui garantit au moins deux etats distincts dans la sequence (l'etat vide
    puis le premier argument arrive, toujours ``in`` au premier pas), donc
    que ``fit_markov_order`` ne rencontre jamais sa condition de rejet
    « moins de deux etats » par cette voie.
    """
    traj = argumentation.belief_trajectory(af, order, include_empty=True)
    if encoding == "summary":
        return [argumentation.belief_summary(lab) for lab in traj]
    if encoding == "signature":
        return [argumentation.state_signature(lab, n_args=af.n()) for lab in traj]
    raise ValueError(
        f"encoding inconnu : {encoding!r} (summary|signature)"
    )


def _comptes_transitions(
    etats: Sequence[Tuple],
    mapping: Dict[Tuple, int],
) -> np.ndarray:
    """Matrice (k, k) des comptes de transitions consecutives.

    Necessaire parce que ``tpm_from_trajectory`` ne rend que la TPM
    **normalisee** (les comptes sont construits puis normalises en interne) :
    ``mdl.tpm_description_length``, lui, mesure une matrice de comptes.
    Le simple denombrement des paires consecutives n'est pas une
    reimplementation de semantique -- la semantique (traduire des comptes en
    bits) reste dans l'organe ``mdl``.
    """
    comptes = np.zeros((len(mapping), len(mapping)), dtype=int)
    for a, b in zip(etats[:-1], etats[1:]):
        comptes[mapping[a], mapping[b]] += 1
    return comptes


# --------------------------------------------------------------------------- #
#  Assemblage du triplet                                                       #
# --------------------------------------------------------------------------- #


def assembler_triplet(
    af: DungAF,
    order: Sequence[int],
    encoding: str = "summary",
    n_permuts: int = 8,
    seed: int = 0,
    max_markov_order: int = 4,
) -> Dict[str, dict]:
    """Rend les trois lectures (sigma, K, ordre) d'un meme debat, sans les agreger.

    Parameters
    ----------
    af : DungAF
        AF complet (tous les arguments possibles + leurs attaques).
    order : sequence d'entiers
        Ordre d'arrivee des arguments = ordre du texte (ordre narratif).
    encoding : ``"summary"`` (defaut) ou ``"signature"``
        Encodage des etats de croyance, cf.
        :func:`ict.argumentation.belief_transition_matrix`.
    n_permuts : int
        Nombre d'ordres permutes tires pour la jambe contre-factuelle.
    seed : int
        Graine du tirage des permutations (reproductibilite).
    max_markov_order : int
        Ordre de Markov maximal teste par :func:`ict.mdl.fit_markov_order`.

    Returns
    -------
    dict a quatre cles :
      - ``"sigma"`` : ``{"tpm", "mapping", "irreversibilite"}`` ou
        ``irreversibilite`` est le retour verbatim de
        :func:`ict.argumentation.discourse_irreversibility`
        (``sigma``, ``pi``, ``P_rev_distance``) ;
      - ``"K"`` : ``{"tpm_bits", "bits_compression", "n_etats",
        "n_transitions"}`` ;
      - ``"ordre"`` : ``{"markov", "permuts"}`` ou ``markov`` est le retour
        de :func:`ict.mdl.fit_markov_order` et ``permuts`` la liste des
        contre-factuels ``{"ordre_permute", "sigma"}`` ;
      - ``"meta"`` : parametres de l'appel (encodage, ordre narratif,
        graine, bornes), pour audit.

    Il n'existe **aucun scalaire au sommet** du retour : le gate est un
    triplet, pas une note. Le sigma a comparer aux contre-factuels permutes
    est ``retour["sigma"]["irreversibilite"]["sigma"]`.

    Raises
    ------
    RefusDeMesure
        ``ENTREE_VIDE`` si ``order`` est vide -- le refus traverse, il ne
        devient jamais un zero.
    ValueError
        Pour un ``encoding`` inconnu (avant toute mesure).
    """
    order = [int(a) for a in order]
    if not order:
        raise RefusDeMesure(
            "ENTREE_VIDE",
            "assembler_triplet : ordre d'arrivee vide, rien a mesurer",
        )

    etats = _encoder_etats(af, order, encoding)
    P, mapping = tpm_estimation.tpm_from_trajectory(etats, unseen="self")
    comptes = _comptes_transitions(etats, mapping)

    # Jambe sigma : l'organe, verbatim, sur la TPM estimee du debat.
    irreversibilite = argumentation.discourse_irreversibility(P)

    # Jambe K : deux instruments cote a cote (MDL deux parties sur les
    # comptes ; zlib sur la sequence canonique d'etats).
    k_leg = {
        "tpm_bits": mdl.tpm_description_length(comptes),
        "bits_compression": compression.compressed_length(etats),
        "n_etats": len(mapping),
        "n_transitions": len(etats) - 1,
    }

    # Jambe ordre : sensibilite a l'ordre de Markov + contre-factuels
    # permutes de l'ordre d'arrivee (#7742, tranche 1). Le meme sigma est
    # recalcule sur chaque ordre permute -- meme organ, autre ordre.
    rng = np.random.default_rng(seed)
    permuts: List[dict] = []
    for _ in range(n_permuts):
        ordre_permute = [int(a) for a in rng.permutation(order)]
        etats_p = _encoder_etats(af, ordre_permute, encoding)
        P_p, _ = tpm_estimation.tpm_from_trajectory(etats_p, unseen="self")
        permuts.append({
            "ordre_permute": ordre_permute,
            "sigma": argumentation.discourse_irreversibility(P_p)["sigma"],
        })

    return {
        "sigma": {
            "tpm": P,
            "mapping": mapping,
            "irreversibilite": irreversibilite,
        },
        "K": k_leg,
        "ordre": {
            "markov": mdl.fit_markov_order(
                etats, heldout=None, max_order=max_markov_order
            ),
            "permuts": permuts,
        },
        "meta": {
            "encoding": encoding,
            "n_arguments": af.n(),
            "ordre_narratif": order,
            "n_permuts": n_permuts,
            "seed": seed,
            "max_markov_order": max_markov_order,
        },
    }
