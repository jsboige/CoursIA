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
) -> dict[str, Any]:
    """Mesure pre-registree : delta_pair vs null croise + delta_ctrl + z features.

    Verdict (critères figés c.5743321902, null corrigé c.5743498870) :
    FEATURE_CANDIDATE ssi delta_pair > p99(null croise) ET delta_pair >
    1.5*delta_ctrl ET >= 3 features |z| > 3 du meme cote ; SURFACE_SEULE si
    delta_pair dépasse le null mais <= 1.5*delta_ctrl ; INCONCLUSIVE sinon.
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
    z = observed / (null_means.std(axis=0) + 1e-12)
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
    return {
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
