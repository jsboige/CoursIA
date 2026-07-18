"""Co-localisation inter-lentilles des ignitions SAE <-> J-Lens (strate 5, #5681 / #4588).

La jambe **lens-agreement** de la triade d'evenements du capstone axe-derivee-temporelle
(#7259). Le tete-a-tete ``ICT-SAE-JLens-TeteATete.ipynb`` (PR #5959) a etabli que les deux
lentilles vivent dans des **espaces disjoints** (features SAE vs directions singulieres
J-space, sec. 8.3) et que leurs *valeurs* de concentration par position ne se correlent que
faiblement. Il n'a PAS teste la question temporelle qui interesse le workspace global : les
deux lentilles **s'allument-elles aux MEMES positions de token** ?

Ce module operationalise cette question de facon falsifiable et **GPU-free** (sur les traces
layer-16 deja extraites, 2699 tokens), en **reutilisant** la primitive deja mergee
:func:`ict.workspace.event_colocalization` (#7274, distance plus-proche-voisin symetrisee +
null par rotation circulaire). Ce module n'ajoute PAS de statistique : il fournit la
**glue inter-lentille** que la primitive laisse explicitement a l'appelant (« l'agregation
multi-prompts vit dans le notebook/appelant, pas ici »).

Pipeline
--------
1. Pour chaque lentille, on tire la **serie de concentration** par position
   (:func:`ict.workspace.concentration_series`, Gini du panel differentiel) puis on detecte
   les **ignitions** (:func:`ict.workspace.ignition_events`, pics persistants, lecture
   Dehaene). Chaque lentille selectionne SES propres features differentielles : la
   concentration scalaire est la **monnaie commune** entre deux espaces disjoints.
2. Les **centres** des ignitions de chaque lentille (indices dans ``[0, T)``) alimentent
   :func:`ict.workspace.event_colocalization` prompt par prompt (memes tokens) : distance
   moyenne au plus proche voisin, symetrisee, contre un null de rotation circulaire.
   La distance plus-proche-voisin **tolere les quasi-coincidences** (deux ignitions proches
   mais non exactement superposees comptent comme un rapprochement) — la bonne question pour
   « les deux lentilles s'allument-elles ensemble », pas « exactement au meme index ».
3. On agrege les verdicts par prompt sur les prompts partages.

**Distinction avec #7274.** ``event_colocalization`` est la primitive pure (deux listes
d'indices). #7274 l'a cablee pour la co-localisation **INTRA-lentille** beauty<->ignition
(deux flux temporels DANS la meme lentille). Ce module la cable pour la co-localisation
**INTER-lentille** SAE<->J-Lens (deux appareils differents sur le meme texte) — complementaire,
pas redondante : c'est la jambe *lens-agreement* de la triade, distincte de la jambe
*beauty<->ignition*.

Verdict falsifiable
-------------------
* ``colocalized`` reproductible sur les prompts -> les deux lentilles allument leurs ignitions
  aux memes positions : un meme evenement de workspace vu par deux appareils (jambe
  lens-agreement CREDITEE).
* ``dissociated`` / ``chance`` -> les deux lentilles s'allument a des positions differentes.
  Verdict negatif **legitime**, coherent avec la dissociation deja observee a ICT-24
  (emergence_gain <-> ignition ~17 % crediees) et le constat « espaces disjoints » du
  tete-a-tete ; il reconnecte le negatif d'ICT-24 a la prediction du Gate 5 de la synthese
  (la jambe temporelle discrimine orthogonalement). A rapporter **honnetement** : ne pas
  vendre une co-localisation qui n'existe pas.

Garde-fou (a reporter dans le notebook consommateur)
----------------------------------------------------
Le ``densify`` du J-Lens est une approximation de **rang-k** (les directions hors top-50 ont
un coefficient petit mais non nul), tandis que le SAE top-k est **exact** par construction
(cf :mod:`ict.jlens_traces`). La concentration J-Lens porte donc cette approximation ; le
verdict de co-localisation se lit avec cette nuance, deja documentee dans le tete-a-tete.
Le compte d'ignitions par lentille (``n_ign_a`` / ``n_ign_b`` par prompt) est reporte pour
juger la **puissance** du test : une lentille qui n'allume presque jamais (J-Lens clairseme
au seuil q=0.9) rend le prompt peu informatif -- le verdict agrege distingue les prompts
``undefined`` (flux vide).

Numpy uniquement : AUCUN import torch (le GPU reste confine aux scripts d'extraction).

References
----------
* Dehaene, Changeux -- ignition temporelle (P3b) que :func:`ict.workspace.ignition_events`
  operationalise.
* Anthropic, *Global Workspace in Claude* (2025) -- substrat J-space (jacobien des logits).
* Grün (2009) -- null par rotation pour le co-firing de trains d'evenements (via #7274).
* Tete-a-tete ``ICT-SAE-JLens-TeteATete.ipynb`` (PR #5959) -- concentration par lentille,
  espaces disjoints (sec. 8.3).
* :func:`ict.workspace.event_colocalization` (#7274) -- primitive reutilisee telle quelle.
* #5681 (tete-a-tete SAE<->J-Lens), #7259 (capstone axe derivee temporelle), #4588 (Epic ICT).
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

import numpy as np

from .workspace import concentration_series, event_colocalization, ignition_events

__all__ = [
    "lens_ignition_centers",
    "colocalize_lenses",
]


# --------------------------------------------------------------------------- #
# Ignitions par lentille -> centres d'evenements alimentant event_colocalization
# --------------------------------------------------------------------------- #
def lens_ignition_centers(
    traces: dict,
    feature_ids: np.ndarray,
    *,
    q: float = 0.9,
    persistence: int = 3,
    metric: str = "gini",
) -> Dict[Tuple[str, int], Tuple[List[int], int]]:
    """Centres d'ignition (+ longueur ``T``) par prompt pour une lentille.

    Pour chaque prompt : concentration par position (:func:`concentration_series`
    du panel differentiel), seuil = **quantile ``q``** de la serie, puis
    :func:`ignition_events`. On retourne la liste des ``center`` (indices dans
    ``[0, T)``) et ``T`` -- exactement le format attendu par
    :func:`ict.workspace.event_colocalization`.

    Le seuil par quantile est calibre **par serie** : deux lentilles de dynamiques
    differentes gardent chacune leurs ~10 % de positions les plus concentrees.
    """
    from .sae_traces import acts_topk_panels

    panels = acts_topk_panels(traces, feature_ids)
    out: Dict[Tuple[str, int], Tuple[List[int], int]] = {}
    for key, dense in panels.items():
        conc = concentration_series(dense, metric)
        T = int(conc.size)
        thr = float(np.quantile(conc, q)) if T else 0.0
        centers = [int(ev["center"]) for ev in ignition_events(conc, thr, persistence=persistence)]
        out[key] = (centers, T)
    return out


# --------------------------------------------------------------------------- #
# Pilote agrege sur les prompts partages des deux lentilles
# --------------------------------------------------------------------------- #
def colocalize_lenses(
    traces_a: dict,
    traces_b: dict,
    *,
    k: int = 64,
    q: float = 0.9,
    persistence: int = 3,
    metric: str = "gini",
    n_null: int = 500,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, object]:
    """Co-localisation agregee des ignitions **inter-lentilles** sur les prompts partages.

    Chaque lentille selectionne SES propres ``k`` features differentielles (espaces
    disjoints, cf tete-a-tete sec. 8.3) ; on co-localise position par position DANS
    chaque prompt partage (memes tokens) via :func:`ict.workspace.event_colocalization`,
    puis on agrege les verdicts.

    Un prompt dont les deux lentilles ne partagent pas la meme longueur ``T`` est
    **saute** (positions non comparables) et compte dans ``n_skipped`` -- garde-fou
    contre une mauvaise paire de fixtures. Un prompt ou une lentille n'allume aucune
    ignition donne ``verdict == "undefined"`` (compte dans ``n_undefined``, exclu des
    moyennes de ``z``).

    Parametres
    ----------
    traces_a, traces_b : dict
        Traces chargees (cf :func:`ict.sae_traces.load_traces` /
        :func:`ict.jlens_traces.load_traces`), memes prompts.
    k, q, persistence, metric
        Cf :func:`lens_ignition_centers` et :func:`ict.sae_traces.differential_features`.
    n_null : int
        Rotations du null par prompt (transmis a :func:`event_colocalization`).
    rng : numpy.random.Generator, optional
        Source aleatoire du null (defaut ``default_rng(0)``, reproductible).

    Retour
    ------
    dict
        ``n_prompts`` (prompts co-localises), ``n_skipped`` / ``skipped`` (T
        incompatible), ``n_undefined`` (une lentille sans ignition),
        ``n_colocalized`` / ``n_dissociated`` / ``n_chance`` (comptes de verdicts),
        ``z_mean`` (moyenne des ``z`` definis ; ``> 0`` = plus proche qu'au hasard),
        ``verdict`` (synthese : ``"colocalized"`` si les prompts co-localises dominent
        strictement les dissocies, ``"dissociated"`` si l'inverse, ``"chance"`` sinon),
        ``per_prompt`` (liste des retours :func:`event_colocalization`, chacun enrichi
        de ``prompt``, ``n_ign_a``, ``n_ign_b``).
    """
    from .sae_traces import differential_features

    if rng is None:
        rng = np.random.default_rng(0)
    feat_a = differential_features(traces_a, k=k)
    feat_b = differential_features(traces_b, k=k)
    ev_a = lens_ignition_centers(traces_a, feat_a, q=q, persistence=persistence, metric=metric)
    ev_b = lens_ignition_centers(traces_b, feat_b, q=q, persistence=persistence, metric=metric)
    shared = sorted(set(ev_a) & set(ev_b))

    per_prompt: List[dict] = []
    skipped: List[dict] = []
    for key in shared:
        centers_a, T_a = ev_a[key]
        centers_b, T_b = ev_b[key]
        if T_a != T_b:
            skipped.append({"prompt": key, "T_a": T_a, "T_b": T_b})
            continue
        r = event_colocalization(centers_a, centers_b, T_a, n_null=n_null, rng=rng)
        r["prompt"] = key
        r["n_ign_a"] = len(centers_a)
        r["n_ign_b"] = len(centers_b)
        per_prompt.append(r)

    n_coloc = sum(1 for r in per_prompt if r["verdict"] == "colocalized")
    n_disso = sum(1 for r in per_prompt if r["verdict"] == "dissociated")
    n_chance = sum(1 for r in per_prompt if r["verdict"] == "chance")
    n_undef = sum(1 for r in per_prompt if r["verdict"] == "undefined")
    zs = [r["z"] for r in per_prompt if not np.isnan(r["z"])]
    z_mean = float(np.mean(zs)) if zs else float("nan")

    if n_coloc > n_disso:
        verdict = "colocalized"
    elif n_disso > n_coloc:
        verdict = "dissociated"
    else:
        verdict = "chance"

    return {
        "n_prompts": len(per_prompt),
        "n_skipped": len(skipped),
        "skipped": skipped,
        "n_undefined": n_undef,
        "n_colocalized": n_coloc,
        "n_dissociated": n_disso,
        "n_chance": n_chance,
        "z_mean": z_mean,
        "verdict": verdict,
        "per_prompt": per_prompt,
    }
