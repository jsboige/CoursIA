"""Profil J-Lens par couche et par position, a dose FIXEE (pilote #15480).

Le piege que ce module ferme (#16230, finding ai-01) : un `interchange` sur
**toutes** les positions et **toutes** les dimensions d'un panneau remplace
l'etat entier par celui du donneur. `TinyTransformer.forward_patched` propage
alors, depuis n'importe quel point d'injection, la trajectoire complete du
donneur -- si bien que la divergence mesuree contre la reference ne depend
plus de la couche ou l'on a injecte. Le profil par couche est **invariant par
construction**, et aucun nombre de seeds ne le repare : ce n'est pas une
mesure bruitee, c'est une mesure qui ne porte pas sur la couche.

La mesure doit donc porter sur une **sous-composante a dose fixee** : un
ensemble de coordonnees de taille k, identique a chaque couche, de sorte que
ce qui varie d'une couche a l'autre soit le point d'injection et rien d'autre.

Ce module ne depend ni du paquet `ict/` ni du dossier de la serie : il prend
les panneaux deja construits. La construction de la spec reste au notebook.
"""

from __future__ import annotations

from typing import Iterable, Sequence

import numpy as np
import torch


def component_coords(weight: np.ndarray, k: int) -> tuple[int, ...]:
    """Les ``k`` coordonnees d'entree les plus chargees d'une sonde lineaire.

    ``weight`` a la forme ``(d_in, d_out)`` : la norme L2 de chaque ligne est
    la charge de la coordonnee d'entree correspondante. Le resultat est trie
    croissant, donc reproductible et comparable entre couches.
    """
    w = np.asarray(weight, dtype=np.float64)
    if w.ndim != 2:
        raise ValueError(f"weight attendu 2-D (d_in, d_out), recu {w.shape}")
    if not 0 < k <= w.shape[0]:
        raise ValueError(f"k={k} hors de [1, {w.shape[0]}]")
    charge = np.linalg.norm(w, axis=1)
    return tuple(int(i) for i in np.sort(np.argsort(charge)[::-1][:k]))


def is_full_panel(
    positions: Sequence[int], features: Sequence[int], shape: tuple[int, ...]
) -> bool:
    """Vrai si la cible couvre tout le panneau -- la mesure serait alors vide.

    ``shape`` est la forme d'un panneau ``(positions, features)``. Le predicat
    est ce qui rend le piege testable : il ne depend pas de la maniere dont la
    spec a ete construite.
    """
    return set(positions) >= set(range(shape[0])) and set(features) >= set(
        range(shape[1])
    )


def kl_final(logits_ref: torch.Tensor, logits_cf: torch.Tensor) -> float:
    """Divergence KL de la distribution next-token a la position finale.

    Les deux cotes passent par `log_softmax` : KL(P||P) vaut alors **exactement**
    0, et le controle de manipulation (re-injecter son propre panneau) se lit a
    1e-9. La formulation naive `p * (log(p + eps) - logq)` -- l'echappatoire
    usuelle a `log(0)` -- pose un plancher de bruit mesure a 7,7e-08 sur ce
    modele : assez petit pour ne pas fausser un effet de 0,1, assez grand pour
    qu'un « zero » ne soit plus distinguable d'un effet reel de cet ordre.
    """
    logp = torch.log_softmax(logits_ref[0, -1], dim=-1)
    logq = torch.log_softmax(logits_cf[0, -1], dim=-1)
    return float((logp.exp() * (logp - logq)).sum().detach())


def layer_effect(
    model,
    tokens: np.ndarray,
    ref_logits: torch.Tensor,
    panel_cf: np.ndarray,
    layer_key: str,
) -> float:
    """KL final entre le forward intact et le forward patche a ``layer_key``."""
    cf = model.forward_patched(
        torch.from_numpy(np.asarray(tokens)[None]),
        {layer_key: torch.from_numpy(np.asarray(panel_cf)[None])},
    )
    return kl_final(ref_logits, cf)


def profile(
    model,
    tokens: np.ndarray,
    ref_logits: torch.Tensor,
    cf_panels: dict[str, np.ndarray],
    layer_keys: Iterable[str],
) -> dict[str, float]:
    """Profil d'effet par couche pour une dose fixee, un contre-factuel par couche."""
    return {
        key: layer_effect(model, tokens, ref_logits, cf_panels[key], key)
        for key in layer_keys
    }


def layer_spread(profile_by_layer: dict[str, float]) -> float:
    """Ecart max-min du profil : zero exactement quand la couche est muette.

    C'est l'instrument de la garde : sous un panneau entier, ce nombre vaut 0
    a la tolerance flottante, quelle que soit la machine et quel que soit le
    modele. Une valeur non nulle prouve que la mesure depend bien du point
    d'injection.
    """
    vals = list(profile_by_layer.values())
    if not vals:
        raise ValueError("profil vide")
    return float(max(vals) - min(vals))
