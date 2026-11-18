# -*- coding: utf-8 -*-
"""Courbe de puissance du seuil ``|z| > 3`` de l'instrument humour (ICT-35).

Ce module complete la lecture « null global sur le maximum » (PR #27208) :
celle-ci dit *si* le seuil ``|z| > 3`` est une borne que l'instrument peut
atteindre sous le null ; celle-ci dit *quelle taille d'effet* il faudrait
pour que la regle de detection (``>= 3 features |z| > 3 du meme cote``)
s'ecole. Les deux lectures se lisent ensemble : sans la seconde, « zero
feature au-dela du seuil » se lit comme une absence de signal, alors que la
courbe dit quel seuil serait meme detectable.

**Les cinq questions de l'organ-first** (regle ``organ-first-implementation``) :

1. *Quelle serie possede la semantique ?* La serie ICT (carnets ICT-35b/35c/35d)
   via ``ict/humor_pairs.py`` : l'instrument (delta_pair, delta_ctrl, z par
   flip de signe intra-paire) et son seuil pre-enregistre ``|z| > 3``.
2. *Peut-on invoquer son module reel ?* Oui : ce module **reutilise** les
   primitives de zone de ``ict.humor_pairs`` (``_common_prefix_len``,
   ``_zone_vec``) et le chargeur ``ict.sae_traces.load_traces``. Aucune
   reimplementation de la construction de zone, aucune reimplementation du
   null : la seule quantite nouvelle est la **dispersion nulle exacte**,
   qui est une consequence algebrique du null de l'instrument (voir
   ``null_norms``).
3. *Que faut-il exporter dans la serie source ?* Rien pour l'instant : les
   deux primitives importees sont deja dans le module source. Si elles
   devenaient privees de fait, l'export a demander serait
   ``zone_diffs`` (les differences humour-unfun par paire) -- c'est la seule
   surface dont ce module a besoin.
4. *Quel temoin negatif l'organe natif fournit-il ?* Le null lui-meme :
   sous ``delta = 0``, la simulation doit reproduire la queue mesuree par
   l'organe natif (probabilite qu'une feature depasse le seuil sous null),
   et la regle de detection ne doit **pas** s'ecoler. C'est le test
   d'integrite de ``ict/tests/test_humor_power.py``.
5. *Quelle autre serie verifie independamment ?* ICT-35b (agregat),
   ICT-35c (profondeur) et ICT-35d (forme) rejouent le meme instrument sur
   les memes traces : une re-execution de 35d avec ce module doit retrouver
   la meme queue nulle que la « Lecture 5 bis ».

**Modele declare.** Sous H1, la statistique observee d'une feature est
``z = z_nul + delta`, ou ``z_nul`` est un tirage du null de l'instrument
(flip de signe intra-paire) et ``delta`` est le deplacement de la moyenne
par paire, exprime **en unites de dispersion nulle** (la meme unite que le
z). Le deplacement est suppose additif sur la moyenne par paire, donc
dispersion de la statistique inchangee : c'est ce qui rend le modele exact
plutot qu'approximatif.

Deux bornes structurent la lecture :

* ``|z| <= sqrt(n)`` -- le z d'une feature est un produit scalaire
  normalise, borne par Cauchy-Schwarz : avec 30 paires, aucune feature ne
  peut depasser ``sqrt(30) = 5.477``. Une courbe de puissance qui
  depasse cette borne decrit un effet inaccessible, pas un instrument
  faible.
* le seuil lui-meme est une **convention** de l'instrument, pas une
  propriete de la loi : la courbe se lit « si le seuil etait ``t``, quel
  effet faudrait-il ? », pas « quel est l'effet reel ? ».
"""
from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path
from typing import Any

import numpy as np

from .humor_pairs import _common_prefix_len, _zone_vec

__all__ = [
    "null_norms",
    "observed_z",
    "power_curve",
    "z_ceiling",
    "zone_diffs",
]

# Seuil pre-enregistre de l'instrument (ICT-35b/35c/35d) : le module ne le
# change pas, il mesure la puissance qu'il porte.
DEFAULT_THRESHOLD = 3.0
# Regle de detection de l'instrument : au moins 3 features au-dela du seuil,
# du meme cote.
DEFAULT_MIN_SAME_SIDE = 3


def zone_diffs(
    traces_path: str | Path,
    pairs: list[dict[str, str]],
) -> np.ndarray:
    """Matrice des differences ``humour - unfun`` par paire, ``(n, d_sae)``.

    Meme construction de zone que ``ict.humor_pairs.measure_humor_differential``
    (prefixe commun token par token, moyenne dense des activations SAE
    top-50 de la zone d'edition) : les primitives sont **importees**, pas
    reecrites.
    """
    from .sae_traces import load_traces

    tr = load_traces(traces_path)
    d_sae = int(tr["meta"]["d_sae"])
    n = len(pairs)
    humour = []
    unfun = []
    for i in range(n):
        eh = tr["prompts"][("humour", i)]
        eu = tr["prompts"][("unfun", i)]
        k = _common_prefix_len(eh["tokens"], eu["tokens"])
        humour.append(_zone_vec(eh, k, d_sae))
        unfun.append(_zone_vec(eu, k, d_sae))
    return np.stack(humour) - np.stack(unfun)


def null_norms(diffs: np.ndarray) -> np.ndarray:
    """Dispersion nulle exacte par feature : ``||diffs_f||_2``.

    Le null de l'instrument est le **flip de signe intra-paire** : la
    moyenne d'une feature sous null vaut ``(1/n) * sum_i s_i diffs_if`` avec
    ``s_i`` independants a moyenne nulle et variance 1. Sa variance est donc
    ``(1/n^2) * sum_i diffs_if^2`` et son ecart-type vaut
    ``||diffs_f||_2 / n`` : c'est la formule **exacte** du null, sans aucun
    tirage. (L'instrument estimait cet ecart-type par ecart-type empirique
    sur 2048 tirages ; la formule exacte en est la limite, a moins de 2 %
    pres sur la dispersion.)
    """
    return np.linalg.norm(np.asarray(diffs, dtype=np.float64), axis=0)


def z_ceiling(n_pairs: int) -> float:
    """Borne superieure du |z| d'une feature : ``sqrt(n)``.

    Le z d'une feature vaut ``<a_f, 1> / ||a_f||`` : Cauchy-Schwarz donne
    ``|z| <= sqrt(n)``. Avec 30 paires, ``5.477`` -- un seuil a 3 n'est donc
    pas hors d'atteinte, mais il ne peut pas l'etre que de justesse.
    """
    return float(np.sqrt(float(n_pairs)))


def observed_z(diffs: np.ndarray) -> np.ndarray:
    """z observe par feature (moyenne par paire / dispersion nulle exacte).

    Les features sans variation (``||diffs_f|| = 0``) n'ont pas de z
    definie : elles sont rendues a 0 et exclues du choix des features
    plantees (elles ne peuvent pas porter un effet).
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    norms = null_norms(diffs)
    safe = np.where(norms > 0, norms, np.inf)
    return diffs.sum(axis=0) / safe


def power_curve(
    diffs: np.ndarray,
    deltas: Sequence[float],
    *,
    n_planted: int = DEFAULT_MIN_SAME_SIDE,
    n_replicates: int = 200,
    seed: int = 42,
    threshold: float = DEFAULT_THRESHOLD,
    min_same_side: int = DEFAULT_MIN_SAME_SIDE,
) -> dict[str, Any]:
    """Puissance de la regle de detection en fonction de l'effet plante.

    Sous H1, ``n_planted`` features sont affectees d'un deplacement
    ``delta`` (en unites de dispersion nulle) ; les autres restent a leur
    tirage nul. La regle de detection est celle de l'instrument : au moins
    ``min_same_side`` features au-dela de ``threshold`` **du meme cote**.

    Chaque replicat est une experience independante : un tirage de signes
    intra-paire (le null de l'instrument), puis l'effet plante. La
    realisation de l'effet est elle aussi aleatoire -- les features
    affectees sont tirees uniformement parmi les features actives -- parce
    que l'on ne sait pas *quelles* features porteraient un effet reel.

    Retourne, pour chaque ``delta`` : la probabilite que la regle
    s'ecole (``p_rule``), la probabilite qu'**au moins une** feature
    depasse le seuil (``p_any``) et le nombre moyen de features au-dela
    (``n_over_mean``). ``delta = 0`` est l'ancre nulle : c'est la queue que
    l'organe natif mesure deja.
    """
    diffs = np.asarray(diffs, dtype=np.float64)
    n_pairs, n_features = diffs.shape
    norms = null_norms(diffs)
    eligible = np.flatnonzero(norms > 0)
    if eligible.size == 0:
        raise ValueError("aucune feature active : le null ne peut pas etre mesure")
    if n_planted > eligible.size:
        raise ValueError(
            f"n_planted={n_planted} > {eligible.size} features actives"
        )
    safe = np.where(norms > 0, norms, np.inf)

    rng = np.random.default_rng(seed)
    counters = {
        float(d): {"rule": 0, "any": 0, "n_over": 0, "max_absz": []}
        for d in deltas
    }
    for _ in range(n_replicates):
        signs = rng.choice(np.array([-1.0, 1.0]), size=n_pairs)
        z_null = (signs[:, None] * diffs).sum(axis=0) / safe
        planted = rng.choice(eligible, size=n_planted, replace=False)
        for delta in deltas:
            z = z_null.copy()
            z[planted] += float(delta)
            over = np.abs(z) > threshold
            n_over = int(over.sum())
            pos = int((z[over] > 0).sum())
            neg = n_over - pos
            counters[float(delta)]["rule"] += int(max(pos, neg) >= min_same_side)
            counters[float(delta)]["any"] += int(n_over >= 1)
            counters[float(delta)]["n_over"] += n_over
            counters[float(delta)]["max_absz"].append(float(np.abs(z).max()))

    rows = []
    for delta in deltas:
        c = counters[float(delta)]
        rows.append(
            {
                "delta": float(delta),
                "p_rule": c["rule"] / n_replicates,
                "p_any": c["any"] / n_replicates,
                "n_over_mean": c["n_over"] / n_replicates,
                "max_absz_median": float(np.median(c["max_absz"])),
            }
        )
    return {
        "rows": rows,
        "n_replicates": int(n_replicates),
        "n_pairs": int(n_pairs),
        "n_features": int(n_features),
        "n_eligible": int(eligible.size),
        "threshold": float(threshold),
        "min_same_side": int(min_same_side),
        "n_planted": int(n_planted),
        "seed": int(seed),
        "z_ceiling": z_ceiling(n_pairs),
    }
