# -*- coding: utf-8 -*-
"""Couche d'acces au corpus humour consolide (CORPUS_DUR) pour #14035.

Depuis l'extraction #20316 (T7'), la source de verite du corpus est l'organe
``MyIA.AI.Notebooks/GameTheory/humour_banc/`` : fichiers de donnees committes
+ chargeur canonique (``organ.py``). ``load_corpus_dur`` delegue a l'organe --
plus d'execution positionnelle des cellules du banc 18c : le chargement est
local (snapshot Argumentum commite), deterministe et sans cle OpenRouter.

Ce module reste la couche ICT : il re-exporte les contrats canoniques de
l'organe (corpus, paires) pour la stabilite des consommateurs (ICT-35*,
tests) et porte la couche de mesure differentielle sur traces SAE
(verdict pre-registre c.5743321902, ecart null corrige c.5743498870 --
numpy uniquement, discipline ict/).
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Any

import numpy as np

# --------------------------------------------------------------------------- #
# Delegation a l'organe GameTheory/humour_banc (extraction #20316)
# --------------------------------------------------------------------------- #


def banc_humour_path() -> Path:
    """Chemin canonique du banc humour consolide, resolu depuis ce module."""
    return (
        Path(__file__).resolve().parents[3]
        / "GameTheory"
        / "GameTheory-18c-Humour-Banc-Python.ipynb"  # consolide #14032
    )


def _load_organ():
    """Charge ``humour_banc/organ.py`` par chemin de fichier resolu.

    GameTheory n'est pas un package importable depuis ict : le chargement par
    localisation de fichier est le pont honnete vers l'organe, insensible au
    cwd (le chemin est ancre sur ``__file__`` de ce module).
    """
    organ_path = banc_humour_path().parent / "humour_banc" / "organ.py"
    spec = importlib.util.spec_from_file_location("humour_banc_organ", organ_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"organe humour introuvable : {organ_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_organ = _load_organ()

# Contrats canoniques re-exportes depuis l'organe (API stable des consommateurs).
LABELS: tuple[str, ...] = _organ.LABELS
validate_corpus = _organ.validate_corpus
label_distribution = _organ.label_distribution
load_pair_edits = _organ.load_pair_edits
build_pairs = _organ.build_pairs
validate_pairs = _organ.validate_pairs
load_typology = _organ.load_typology


def load_corpus_dur() -> list[dict[str, Any]]:
    """Charge ``CORPUS_DUR`` depuis l'organe committé (fichiers humour_banc/).

    Deterministe (le corpus est un fichier figé ; la derivation d'origine --
    snapshot Argumentum, heuristiques, seed 42 -- reste rejouable et est
    temoigne en live par la cellule de chargement du banc 18c). Aucune cle
    d'API n'est requise : OPENROUTER_API_KEY ne sert qu'au detecteur LLM du
    banc, qui la verifie a son point d'usage.
    """
    return _organ.load_corpus()


def build_prompts_json(pairs: list[dict[str, str]]) -> dict[str, list[str]]:
    """Serialise les paires au contrat ``extract_sae_traces.py --prompts-json``.

    Contrat (validateur du script, ligne 663) : dict non vide
    ``{set_name: [textes non vides]}`` -- un texte par paire, ordre stable.
    """
    return {
        "humour": [p["humour"] for p in pairs],
        "unfun": [p["unfun"] for p in pairs],
        "ctrl_edit": [p["ctrl_edit"] for p in pairs],
    }


# --------------------------------------------------------------------------- #
# Mesure differentielle sur traces SAE (verdict pre-registre c.5743321902,
# ecart null corrigé c.5743498870 — numpy uniquement, discipline ict/)
# --------------------------------------------------------------------------- #

def _common_prefix_len(toks_a, toks_b) -> int:
    """Longueur du prefixe token commun exact (limite de zone d'edition)."""
    n = 0
    for a, b in zip(toks_a, toks_b):
        if a != b:
            break
        n += 1
    return n


def _zone_vec(entry: dict, start: int, d_sae: int) -> np.ndarray:
    """Vecteur moyen dense (d_sae,) des activations des tokens de zone."""
    ids = entry["ids"][start:]
    vals = entry["vals"][start:]
    assert ids.shape[0] > 0, "zone d'edition vide (prefixe commun = texte entier)"
    v = np.zeros(d_sae, dtype=np.float64)
    np.add.at(v, ids.ravel(), vals.ravel())
    return v / ids.shape[0]


def measure_humor_differential(
    traces_path: str | Path,
    pairs: list[dict[str, str]],
    *,
    n_draws: int = 2048,
    seed: int = 42,
    with_null_max: bool = False,
) -> dict[str, Any]:
    """Mesure pre-registree : delta_pair vs null croise + delta_ctrl + z features.

    Verdict (critères figés c.5743321902, null corrigé c.5743498870) :
    FEATURE_CANDIDATE ssi delta_pair > p99(null croise) ET delta_pair >
    1.5*delta_ctrl ET >= 3 features |z| > 3 du meme cote ; SURFACE_SEULE si
    delta_pair dépasse le null mais <= 1.5*delta_ctrl ; INCONCLUSIVE sinon.

    ``with_null_max`` ajoute les statistiques du null **sur le maximum**
    (``null_max_absz`` : max |z| par tirage ; ``null_over3`` : compte de
    features au-dela de 3 sigma par tirage ; ``z_max_observed``). Elles ne
    consomment pas de tirage supplementaire : elles sont lues dans le tableau
    de null deja calcule. Le role est decrit dans ``summarize_global_max_null``.
    """
    from .sae_traces import load_traces

    tr = load_traces(traces_path)
    d_sae = int(tr["meta"]["d_sae"])
    n = len(pairs)
    zones = {"humour": [], "unfun": [], "ctrl_edit": []}
    for i in range(n):
        eh = tr["prompts"][("humour", i)]
        eu = tr["prompts"][("unfun", i)]
        ec = tr["prompts"][("ctrl_edit", i)]
        k_hu = _common_prefix_len(eh["tokens"], eu["tokens"])
        k_hc = _common_prefix_len(eh["tokens"], ec["tokens"])
        zones["humour"].append(_zone_vec(eh, k_hu, d_sae))
        zones["unfun"].append(_zone_vec(eu, k_hu, d_sae))
        zones["ctrl_edit"].append(_zone_vec(ec, k_hc, d_sae))
    H = np.stack(zones["humour"])       # [n, d_sae]
    U = np.stack(zones["unfun"])
    C = np.stack(zones["ctrl_edit"])

    delta_pair = float(np.mean(np.abs(H - U).sum(axis=1)))
    delta_ctrl = float(np.mean(np.abs(H - C).sum(axis=1)))

    rng = np.random.default_rng(seed)
    # Null croise (c.5743498870) : sigma brasse les unfun ENTRE paires.
    null_deltas = np.empty(n_draws)
    for d in range(n_draws):
        sigma = rng.permutation(n)
        null_deltas[d] = np.mean(np.abs(H - U[sigma]).sum(axis=1))
    p99 = float(np.quantile(null_deltas, 0.99))

    # z features : flip de signe intra-paire (null valide au niveau feature).
    diffs = H - U                                  # [n, d_sae]
    observed = diffs.mean(axis=0)
    null_means = np.empty((n_draws, d_sae))
    for d in range(n_draws):
        s = rng.choice(np.array([-1.0, 1.0]), size=(n, 1))
        null_means[d] = (diffs * s).mean(axis=0)
    null_std = null_means.std(axis=0)
    z = observed / (null_std + 1e-12)
    over = np.where(np.abs(z) > 3)[0]
    pos = sum(1 for f in over if z[f] > 0)
    neg = len(over) - pos
    same_side = max(pos, neg) >= 3

    if delta_pair > p99 and delta_pair > 1.5 * delta_ctrl and same_side:
        verdict = "FEATURE_CANDIDATE"
    elif delta_pair > p99:
        verdict = "SURFACE_SEULE"
    else:
        verdict = "INCONCLUSIVE"
    res = {
        "delta_pair": delta_pair,
        "delta_ctrl": delta_ctrl,
        "null_p99": p99,
        "ratio_vs_ctrl": delta_pair / max(delta_ctrl, 1e-12),
        "n_features_over3": int(len(over)),
        "n_over3_positive": int(pos),
        "n_over3_negative": int(neg),
        "top_features": sorted(
            ((int(f), float(z[f])) for f in np.argsort(np.abs(z))[::-1][:10]),
            key=lambda x: -abs(x[1]),
        ),
        "verdict": verdict,
    }
    if with_null_max:
        max_absz, over_null = _null_max_stats(null_means, null_std)
        res["z_max_observed"] = float(np.abs(z).max())
        res["null_max_absz"] = max_absz
        res["null_over3"] = over_null
    return res


# --------------------------------------------------------------------------- #
# Null global sur le maximum : le seuil "3 sigma" face au maximum que le null
# atteint lui-meme, sur le dictionnaire entier
# --------------------------------------------------------------------------- #

# Le critere ">= 3 features |z| > 3" se lit comme une absence de signal quand
# le compte vient a zero. Mais le seuil 3 n'est pas une constante naturelle du
# dictionnaire : le z d'une feature est un rapport (une moyenne de 30 paires
# divisee par son ecart-type sous null), les features inertes ont un ecart-type
# nul, et les features actives ne sont ni independantes ni normales. Le seul
# yardstick honnete est donc le maximum que le null atteint lui-meme, mesure
# sur la meme construction et le meme tirage de signes.
#
# Ce yardstick est un taux de depassement SOUS H0 (P_H0(max |z| > seuil)).
# Ce n'est pas une puissance : la puissance d'un seuil est une probabilite de
# rejection sous une alternative explicitee, que ce module ne calcule pas et
# ne pretend pas estimer.


def _null_max_stats(
    null_means: np.ndarray,
    null_std: np.ndarray,
    *,
    threshold: float = 3.0,
    chunk: int = 128,
) -> tuple[np.ndarray, np.ndarray]:
    """Maximum |z| et compte de features au-dela du seuil, par tirage du null.

    Le z d'un tirage est ``null_means[d, f] / null_std[f]`` : meme construction
    que le z observe. Les tirages sont traites par blocs -- un second tableau
    (n_draws, d_sae) materialise depasse vite le gigaoctet.
    """
    n_draws = null_means.shape[0]
    denom = null_std + 1e-12
    max_absz = np.empty(n_draws, dtype=np.float64)
    over = np.empty(n_draws, dtype=np.int64)
    for start in range(0, n_draws, chunk):
        block = np.abs(null_means[start:start + chunk] / denom)
        max_absz[start:start + chunk] = block.max(axis=1)
        over[start:start + chunk] = (block > threshold).sum(axis=1)
    return max_absz, over


def summarize_global_max_null(
    max_absz: np.ndarray,
    over_null: np.ndarray,
    *,
    z_max_observed: float,
    n_over_observed: int,
    threshold: float = 3.0,
) -> dict[str, Any]:
    """Verdict du seuil "3 sigma" face au null global du dictionnaire.

    Quatre lectures possibles :

    * ``SIGNAL_HORS_NULL`` -- les donnees produisent une feature au-dela du
      seuil et le maximum observe sort de la plage du null (au-dessus de son
      99e centile).
    * ``ABSENCE_DEVIATE_DU_NULL`` -- les donnees ne produisent aucune feature
      au-dela du seuil alors que le null en produit rarement (probabilite
      d'un zero sous le null <= 0.05) : l'absence est alors notable.
    * ``ABSENCE_NON_INFORMATIVE`` -- les donnees ne produisent aucune feature
      au-dela du seuil, et le null en produit *souvent* zero : le zero observe
      est l'issue typique du null, il ne distingue rien. Ce verdict qualifie
      l'observation (elle ne departage pas le null) ; il n'etablit pas la
      sensibilite de l'instrument, qui exigerait une alternative explicitee.
    * ``CONFORME_AU_NULL`` -- les donnees produisent des features au-dela du
      seuil a un rythme comparable a celui du null.

    Les quantites de ``null_features_over_seuil`` sont des **taux de
    depassement sous l'hypothèse nulle** : ``frac_draws_with_one`` vaut
    ``P_H0(max |z| > seuil)``, c'est-a-dire la frequence a laquelle le null
    lui-meme atteint le seuil. Ce n'est pas une puissance : une puissance se
    mesure sous une alternative explicitee (effet specifie, plusieurs
    repetitions).
    """
    max_absz = np.asarray(max_absz, dtype=np.float64)
    over_null = np.asarray(over_null, dtype=np.int64)
    null_max = {
        "median": float(np.median(max_absz)),
        "q95": float(np.quantile(max_absz, 0.95)),
        "q99": float(np.quantile(max_absz, 0.99)),
        "max": float(max_absz.max()),
    }
    null_count = {
        "median": float(np.median(over_null)),
        "q95": float(np.quantile(over_null, 0.95)),
        "max": int(over_null.max()),
        "frac_draws_with_one": float((over_null > 0).mean()),
    }
    # Probabilite que le null produise *aucune* feature au-dela du seuil :
    # c'est la reference contre laquelle se lit un compte observe a zero.
    p_zero_under_null = float((over_null == 0).mean())
    null_count["p_zero_under_null"] = p_zero_under_null
    p_max_ge_observed = float((max_absz >= z_max_observed).mean())
    seuil_atteignable = bool(null_max["max"] >= threshold)
    if n_over_observed >= 1 and p_max_ge_observed <= 0.01:
        verdict = "SIGNAL_HORS_NULL"
    elif n_over_observed == 0 and p_zero_under_null <= 0.05:
        verdict = "ABSENCE_DEVIATE_DU_NULL"
    elif n_over_observed == 0:
        verdict = "ABSENCE_NON_INFORMATIVE"
    else:
        verdict = "CONFORME_AU_NULL"
    return {
        "seuil": float(threshold),
        "z_max_observed": float(z_max_observed),
        "n_features_over_seuil_observe": int(n_over_observed),
        "null_max_absz": null_max,
        "null_features_over_seuil": null_count,
        "p_max_null_ge_observe": p_max_ge_observed,
        "p_zero_under_null": p_zero_under_null,
        "seuil_atteignable_sous_null": seuil_atteignable,
        "verdict": verdict,
    }


def measure_global_max_null(
    traces_path: str | Path,
    pairs: list[dict[str, str]],
    *,
    n_draws: int = 2048,
    seed: int = 42,
) -> dict[str, Any]:
    """Null global sur le maximum : version autonome de l'instrument.

    Mesure la meme construction que ``measure_humor_differential`` (null par
    flip de signe intra-paire) et ajoute la distribution du max |z| sur le
    dictionnaire entier : c'est elle qui dit si le seuil "3 sigma" est une
    borne que cet instrument peut atteindre.
    """
    res = measure_humor_differential(
        traces_path, pairs, n_draws=n_draws, seed=seed, with_null_max=True
    )
    max_absz = res.pop("null_max_absz")
    over_null = res.pop("null_over3")
    z_max = res.pop("z_max_observed")
    out = summarize_global_max_null(
        max_absz,
        over_null,
        z_max_observed=z_max,
        n_over_observed=res["n_features_over3"],
    )
    out["n_features_over3"] = res["n_features_over3"]
    out["verdict_measure"] = res["verdict"]
    return out
