"""Mesures F-Lens sur capture dense des residus du banc 20 prompts (#17740).

F-Lens (ICT-36, grain #15478) lit la **geometrie factorisee** des residus :
dimension effective (NC@p) par prompt, et alignement des sous-espaces
principaux entre prompts — meme jeu vs jeux differents — contre une hypothese
nulle appariee. Ce module transpose la lentille du substrat synthetique du
pilote vers le banc 9B de la couche 16, sur la capture dense produite par
``scripts/extract_dense_traces.py`` (meme prompts/tokenisation que les traces
SAE ICT-21 et J-Lens ICT-24 — l'alignement est verifie par l'appelant).

Numpy-only : la serie garde le torch confine dans ``scripts/``.

L'hypothese nulle suit la prescription de :func:`ict.factor_geometry.\
null_overlap_distribution` — sa propre docstring documente que la primitive
est un artefact pedagogique et que le VRAI test passe par des **paires de
sous-espaces aleatoires appariees**. C'est ce que fait :func:`null_pairs`
ci-dessous, en reutilisant exactement les memes statistiques que les paires
reelles (meme chemin de code, pas un calcul parallele qui divergerait).
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .factor_geometry import (
    basis_overlap,
    max_principal_angle,
    nc_at,
    weighted_pca,
)

__all__ = [
    "load_dense",
    "prompt_geometry",
    "pair_statistics",
    "null_pairs",
    "measure_flens",
]

#: Champs de ``__meta__`` exigés — le contrat d'alignement du contraste
#: quadri-instruments porte sur ces quatre-là (cf. geometry_contrast.contrast).
REQUIRED_META = ("model", "layer", "seed", "variant", "d_model")


def load_dense(path: str | Path) -> dict:
    """Charge une capture dense ``ict25_dense_layer<L>_<variant>.npz``.

    Structure miroir des traces SAE/J-Lens : ``__meta__`` JSON +, par prompt
    ``{set}__{i}``, les cles ``__tokens`` (T,) str et ``__resid`` (T, d_model).
    Renvoie ``{"meta": {...}, "prompts": {("set", i): {"tokens", "resid"}}}``
    avec ``resid`` en float32. Refuse une trace partielle (tokens sans resid)
    plutot que la presenter comme complete.
    """
    z = np.load(Path(path), allow_pickle=False)
    if "__meta__" not in z.files:
        raise ValueError(f"{Path(path).name} : pas de __meta__ — pas une trace dense.")
    meta = json.loads(str(z["__meta__"]))
    for key in REQUIRED_META:
        if meta.get(key) is None:
            raise ValueError(f"{Path(path).name} : __meta__ sans {key} "
                             "(contrat d'alignement invalide).")
    d_model = int(meta["d_model"])
    token_keys = sorted(k for k in z.files if k.endswith("__tokens"))
    if not token_keys:
        raise ValueError(f"{Path(path).name} : aucun prompt — trace vide.")
    prompts: dict[tuple[str, int], dict] = {}
    for tok_key in token_keys:
        base = tok_key[: -len("__tokens")]
        set_name, idx = base.rsplit("__", 1)
        resid_key = f"{base}__resid"
        if resid_key not in z.files:
            raise ValueError(f"{Path(path).name} : {base} a des tokens sans "
                             f"{resid_key} — trace partielle, refusee.")
        tokens = z[tok_key]
        resid = z[resid_key].astype(np.float32)
        if resid.ndim != 2 or resid.shape != (len(tokens), d_model):
            raise ValueError(
                f"{Path(path).name} : {base} resid {resid.shape} incoherent "
                f"avec tokens ({len(tokens)},) et d_model={d_model}.")
        if not np.isfinite(resid).all():
            raise ValueError(f"{Path(path).name} : {base} resid non fini — "
                             "chargement de poids probablement casse.")
        prompts[(set_name, int(idx))] = {"tokens": tokens, "resid": resid}
    return {"meta": meta, "prompts": prompts}


def prompt_geometry(resid: np.ndarray,
                    thresholds: tuple[int, ...] = (80, 90, 95, 99)) -> dict:
    """Dimension effective (NC@p) et spectre d'un prompt.

    ``weighted_pca`` sans poids (egalitaire par token, comme la cellule 5
    d'ICT-36) ; ``nc_at`` compte les composantes pour chaque seuil de
    variance cumulee. ``evr_top`` garde les 8 premieres pour le rapport.
    """
    _, _, _, evr = weighted_pca(resid)
    return {
        "nc_at": {str(k): int(v) for k, v in nc_at(evr, thresholds).items()},
        "evr_top": [round(float(x), 5) for x in evr[:8]],
        "n_tokens": int(resid.shape[0]),
        "dim": int(resid.shape[1]),
    }


def _basis_statistics(b_a: np.ndarray, b_b: np.ndarray) -> dict:
    """Comparaison de deux bases orthonormales (D, k) — chemin code partage.

    Utilise tel quel par les paires reelles (apres PCA) et par la nulle
    (bases QR) : les statistiques observee et nulle ne peuvent pas diverger
    de calcul. ``frobenius_alignment`` = ``||B1t B2||_F / sqrt(k)`` : 1.0 =
    memes sous-espaces, ~``sqrt(k/dim)`` pour deux sous-espaces aleatoires.
    La moyenne simple des |cos|, elle, vaut 1/k pour des bases identiques
    (seule la diagonale est non nulle) et descend SOUS le hasard quand k
    grandit — piege mesure, statistique rejetee.
    """
    overlap = basis_overlap(b_a, b_b)
    return {
        "frobenius_alignment": float(np.linalg.norm(overlap, "fro")
                                     / np.sqrt(b_a.shape[1])),
        "max_principal_angle_deg": float(max_principal_angle(b_a, b_b)),
    }


def pair_statistics(resid_a: np.ndarray, resid_b: np.ndarray,
                    top_k: int) -> dict:
    """Alignement des top-k sous-espaces principaux de deux prompts.

    PCA ponderee egalitaire par prompt, puis comparaison des top-k via
    :func:`_basis_statistics` (frobenius_alignment + angle principal max,
    0 deg = memes sous-espaces, 90 = orthogonaux).
    """
    _, comp_a, _, _ = weighted_pca(resid_a)
    _, comp_b, _, _ = weighted_pca(resid_b)
    return _basis_statistics(comp_a[:, :top_k], comp_b[:, :top_k])


def null_pairs(dim: int, top_k: int, n_nulls: int = 200,
               seed: int = 0) -> dict[str, np.ndarray]:
    """Hypothese nulle appariee : statistiques de paire entre sous-espaces
    aleatoires orthonormaux de memes dimensions (dim, top_k).

    Les bases nulles sont PAS des activations : pas de PCA dessus (un PCA
    d'une base orthonormale (dim, top_k) lue comme (N, D) rendrait R^top_k
    entier et un alignement de 1.0 systematique — piege mesure). Les bases
    passent directement a :func:`_basis_statistics`, le meme comparateur que
    les paires reelles. Cf. l'avertissement de
    ``factor_geometry.null_overlap_distribution`` : c'est la paire appariee
    qui est le test, pas l'overlap interne d'une base isolee.
    """
    if top_k < 1 or top_k > dim:
        raise ValueError(f"top_k ({top_k}) hors [1, dim={dim}].")
    rng = np.random.default_rng(seed)
    frob, ang = [], []
    for _ in range(n_nulls):
        q_a = np.linalg.qr(rng.standard_normal((dim, top_k)))[0]
        q_b = np.linalg.qr(rng.standard_normal((dim, top_k)))[0]
        stats = _basis_statistics(q_a.astype(np.float64), q_b.astype(np.float64))
        frob.append(stats["frobenius_alignment"])
        ang.append(stats["max_principal_angle_deg"])
    return {"frobenius_alignment": np.array(frob),
            "max_principal_angle_deg": np.array(ang)}


def measure_flens(dense: dict, *, top_k: int = 16, n_null: int = 200,
                  thresholds: tuple[int, ...] = (80, 90, 95, 99),
                  seed: int = 0) -> dict:
    """Mesure F-Lens complete sur une capture dense alignee.

    Renvoie la geometrie par prompt (NC@p), les agregats d'alignement
    intra-jeu / inter-jeux et la comparaison a la nulle appariee. Les
    verdicts ``beyond_null`` comparent la moyenne observed au quantile 95
    (cos) / 5 (angle, plus bas = plus aligne) de la nulle : un verdict faux
    n'est pas une absence de structure factorisee, seulement une structure
    qui ne se lit pas au seuil choisi au-dessus du hasard.
    """
    prompts = dense["prompts"]
    dim = int(dense["meta"]["d_model"])
    per_prompt = [
        {"prompt": [name, idx], **prompt_geometry(p["resid"], thresholds)}
        for (name, idx), p in sorted(prompts.items())
    ]
    keys = sorted(prompts)
    same_frob, cross_frob, same_ang, cross_ang = [], [], [], []
    for i, key_a in enumerate(keys):
        for key_b in keys[i + 1:]:
            stats = pair_statistics(prompts[key_a]["resid"],
                                    prompts[key_b]["resid"], top_k)
            same = key_a[0] == key_b[0]
            (same_frob if same else cross_frob).append(
                stats["frobenius_alignment"])
            (same_ang if same else cross_ang).append(
                stats["max_principal_angle_deg"])
    nulls = null_pairs(dim, top_k, n_nulls=n_null, seed=seed)

    def _agg(values: list[float]) -> dict | None:
        if not values:
            return None
        arr = np.asarray(values, dtype=np.float64)
        return {"n_pairs": int(arr.size), "mean": float(arr.mean()),
                "min": float(arr.min()), "max": float(arr.max())}

    null_frob_q95 = float(np.quantile(nulls["frobenius_alignment"], 0.95))
    null_ang_q05 = float(np.quantile(nulls["max_principal_angle_deg"], 0.05))
    same = _agg(same_frob)
    cross = _agg(cross_frob)
    verdicts = {
        "same_set_beyond_null_q95": (
            None if same is None
            else bool(same["mean"] > null_frob_q95)),
        "cross_set_beyond_null_q95": (
            None if cross is None
            else bool(cross["mean"] > null_frob_q95)),
    }
    return {
        "status": "measured",
        "top_k": int(top_k),
        "n_null": int(n_null),
        "per_prompt": per_prompt,
        "alignment": {
            "same_set": {"frobenius_alignment": same,
                         "max_principal_angle_deg": _agg(same_ang)},
            "cross_set": {"frobenius_alignment": cross,
                          "max_principal_angle_deg": _agg(cross_ang)},
            "null_paired": {
                "frobenius_alignment": {
                    "mean": float(nulls["frobenius_alignment"].mean()),
                    "q95": null_frob_q95},
                "max_principal_angle_deg": {
                    "mean": float(nulls["max_principal_angle_deg"].mean()),
                    "q05": null_ang_q05},
            },
            "verdicts": verdicts,
        },
        "interpretation": (
            "NC@p : nombre de composantes pour p % de variance cumulee. "
            "frobenius_alignment = ||B1t B2||_F / sqrt(k) : 1.0 = memes "
            "sous-espaces, ~sqrt(k/dim) pour deux sous-espaces aleatoires ; "
            "la nulle appariee fixe le seuil q95. Un verdict faux n'est pas "
            "une absence de structure — c'est une structure indistinguable "
            "du hasard a ce seuil, rapportee comme telle."
        ),
    }
