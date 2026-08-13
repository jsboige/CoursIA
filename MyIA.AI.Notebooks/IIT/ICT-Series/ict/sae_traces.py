"""Chargement et curation GPU-free des traces SAE d'ICT-21 (strate 5, #5101).

Outille le notebook **ICT-21 -- SAETrajectoires** et tout l'aval S4 (#5102
LLMSubstrat, #5635 WorkspaceIgnition) : le pipeline GPU
(:mod:`scripts.extract_sae_traces`) stocke pour chaque token la representation
**sparse exhaustive** du SAE top-k officiel Qwen-Scope (indices + valeurs du
top-50). Toute activation hors top-50 vaut **exactement zero** par construction
du SAE top-k : la densification ici est donc *exacte*, pas une approximation.

Ce module est un **adaptateur mince** (precedent :mod:`ict.feature_dynamics`) :

* :func:`load_traces` -- recharge un ``.npz`` d'extraction (sans pickle) en
  structure par (jeu de prompts, index de prompt) ;
* :func:`densify` -- materialise [T, F] dense pour un sous-ensemble de
  features, depuis le sparse (ids, vals) ;
* :func:`mean_activation_by_set` -- vecteur d'activation moyenne [d_sae] par
  jeu de prompts, accumule depuis le sparse ;
* :func:`differential_features` -- selection top-K des features qui
  *discriminent les regimes* (variance inter-jeux de l'activation moyenne) :
  c'est le ``acts_topk`` (K~64) du schema amende de #5101 ;
* :func:`binarize_quantile` / :func:`states_from_panel` -- panel binarise
  (~10 features) -> codes d'etats discrets consommables par
  :func:`ict.synthesis.emergence_gain` (meme discipline de creditation que
  S1-S3, aucune complaisance nouvelle).

Numpy uniquement : AUCUN import torch ici (regle d'architecture de la serie,
le GPU est confine au script d'extraction).
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

__all__ = [
    "load_traces",
    "densify",
    "mean_activation_by_set",
    "differential_features",
    "acts_topk_panels",
    "binarize_quantile",
    "states_from_panel",
    # Garde-fous cross-echelle (9B/W64K <-> 2B/W32K)
    "resolve_capture_layer",
    "check_sae_model_match",
    "assert_bf16_readout",
    "assert_sae_topk_compatible",
    "trace_filename",
]


# --------------------------------------------------------------------------- #
# Chargement
# --------------------------------------------------------------------------- #
def load_traces(path: str | Path) -> dict:
    """Recharge un ``.npz`` produit par ``scripts/extract_sae_traces.py``.

    Retourne ``{"meta": dict, "prompts": {(set_name, i): {"ids", "vals",
    "tokens"}}}`` avec ``ids`` [T, k] int32, ``vals`` [T, k] float32 (depuis
    float16), ``tokens`` [T] str. Aucun ``allow_pickle`` requis.
    """
    data = np.load(Path(path), allow_pickle=False)
    meta = json.loads(str(data["__meta__"]))
    prompts: dict[tuple[str, int], dict] = {}
    for key in data.files:
        if key == "__meta__":
            continue
        set_name, idx, field = key.rsplit("__", 2)
        entry = prompts.setdefault((set_name, int(idx)), {})
        if field == "topk_ids":
            entry["ids"] = data[key].astype(np.int32)
        elif field == "topk_vals":
            entry["vals"] = data[key].astype(np.float32)
        elif field == "tokens":
            entry["tokens"] = data[key]
    for (set_name, idx), entry in prompts.items():
        missing = {"ids", "vals"} - set(entry)
        if missing:
            raise ValueError(f"trace {set_name}__{idx} incomplete : manque {missing}")
    return {"meta": meta, "prompts": prompts}


# --------------------------------------------------------------------------- #
# Densification exacte depuis le sparse top-k
# --------------------------------------------------------------------------- #
def densify(ids: np.ndarray, vals: np.ndarray, feature_ids: np.ndarray) -> np.ndarray:
    """Materialise [T, F] dense pour ``feature_ids``, exact par construction.

    Une feature absente du top-50 d'un token a une activation exactement nulle
    (SAE top-k) : aucun biais de troncature.
    """
    feature_ids = np.asarray(feature_ids, dtype=np.int64)
    T = ids.shape[0]
    dense = np.zeros((T, feature_ids.size), dtype=np.float32)
    # position de chaque id du top-k dans feature_ids (ou -1)
    order = np.argsort(feature_ids)
    sorted_feats = feature_ids[order]
    pos = np.searchsorted(sorted_feats, ids)
    pos = np.clip(pos, 0, sorted_feats.size - 1)
    hit = sorted_feats[pos] == ids                       # [T, k] bool
    rows = np.broadcast_to(np.arange(T)[:, None], ids.shape)
    dense[rows[hit], order[pos[hit]]] = vals[hit]
    return dense


def mean_activation_by_set(traces: dict) -> dict[str, np.ndarray]:
    """Activation moyenne [d_sae] par jeu de prompts, accumulee du sparse."""
    d_sae = int(traces["meta"]["d_sae"])
    sums: dict[str, np.ndarray] = {}
    counts: dict[str, int] = {}
    for (set_name, _), entry in traces["prompts"].items():
        acc = sums.setdefault(set_name, np.zeros(d_sae, dtype=np.float64))
        np.add.at(acc, entry["ids"].ravel(), entry["vals"].ravel().astype(np.float64))
        counts[set_name] = counts.get(set_name, 0) + entry["ids"].shape[0]
    return {s: (acc / counts[s]).astype(np.float32) for s, acc in sums.items()}


def differential_features(traces: dict, k: int = 64) -> np.ndarray:
    """Top-``k`` features par variance inter-jeux de l'activation moyenne.

    C'est la selection ``acts_topk`` du schema amende de #5101 : les features
    qui *discriminent les regimes* (code vs prose vs dialogue...), pas les plus
    actives en absolu (qui seraient dominees par la ponctuation/le formatage).
    """
    means = mean_activation_by_set(traces)
    stack = np.stack(list(means.values()))               # [n_sets, d_sae]
    score = stack.var(axis=0)
    return np.argsort(score)[::-1][:k].astype(np.int64)


def acts_topk_panels(traces: dict, feature_ids: np.ndarray) -> dict[tuple[str, int], np.ndarray]:
    """Panels denses [T, K] float32 par prompt pour ``feature_ids`` (schema amende)."""
    return {key: densify(e["ids"], e["vals"], feature_ids)
            for key, e in traces["prompts"].items()}


# --------------------------------------------------------------------------- #
# Panel binarise -> etats discrets (consommable par ict.synthesis)
# --------------------------------------------------------------------------- #
def binarize_quantile(dense: np.ndarray, q: float = 0.5) -> np.ndarray:
    """Binarise [T, F] par seuil au quantile ``q`` des valeurs POSITIVES de
    chaque feature (les zeros structurels du top-k n'ecrasent pas le seuil).

    Une feature jamais active sur la fenetre reste toute a False.
    """
    if not 0.0 <= q < 1.0:
        raise ValueError(f"quantile q={q} hors [0, 1)")
    T, F = dense.shape
    bits = np.zeros((T, F), dtype=bool)
    for j in range(F):
        col = dense[:, j]
        pos = col[col > 0]
        if pos.size == 0:
            continue
        bits[:, j] = col > np.quantile(pos, q)
    return bits


def states_from_panel(bits: np.ndarray) -> np.ndarray:
    """Encode chaque ligne binaire en un code d'etat entier (bit-packing).

    Limite volontaire a 20 features (2^20 etats) : au-dela, l'estimation de
    TPM d':func:`ict.synthesis.emergence_gain` n'aurait de toute facon plus
    aucun support statistique sur quelques milliers de tokens.
    """
    T, F = bits.shape
    if F > 20:
        raise ValueError(f"panel a {F} features : bit-packing limite a 20 "
                         "(explosion d'etats vs support statistique)")
    weights = (1 << np.arange(F)).astype(np.int64)
    return bits.astype(np.int64) @ weights


# --------------------------------------------------------------------------- #
# Garde-fous cross-echelle (9B/W64K <-> 2B/W32K) — #5105 / #7396
#
# Ces quatre fonctions sont volontairement pures (aucun torch, aucun reseau) :
# elles decrivent le contrat d'une extraction SAE, donc elles doivent etre
# testables sans GPU, et le script d'extraction les consomme au lieu de
# reimplementer les memes verifications en ligne.
# --------------------------------------------------------------------------- #
def resolve_capture_layer(n_layers: int,
                          layer: int | None = None,
                          layer_frac: float | None = None) -> dict:
    """Resout la couche de capture et rend sa **profondeur relative**.

    Le piege que cette fonction existe pour fermer : ``--layer 16`` est
    silencieusement comparable a lui-meme d'une echelle a l'autre alors qu'il
    ne l'est pas. Sur ``Qwen3.5-9B-Base`` (32 couches) la couche 16 est le
    mi-reseau ; sur ``Qwen3.5-2B-Base`` (24 couches) c'est **deux tiers** de la
    profondeur. Un differentiel de features entre les deux melangerait alors
    l'effet cherche et un simple artefact de profondeur, **sans jamais lever
    d'erreur** — le mode de defaillance le plus couteux qui soit.

    Passer ``layer_frac`` rend l'intention explicite et transposable :
    ``0.5`` donne 16 sur le 9B (16/31) et 12 sur le 2B (12/23).

    Exactement un des deux parametres doit etre fourni.
    """
    if (layer is None) == (layer_frac is None):
        raise ValueError("fournir exactement un de layer / layer_frac "
                         f"(recu layer={layer}, layer_frac={layer_frac})")
    if n_layers is None or n_layers < 1:
        raise ValueError(f"n_layers invalide : {n_layers!r} — la config du "
                         "modele n'expose pas num_hidden_layers")
    if layer_frac is not None:
        if not 0.0 <= layer_frac <= 1.0:
            raise ValueError(f"layer_frac={layer_frac} hors [0, 1]")
        layer = int(round(layer_frac * (n_layers - 1)))
    if not 0 <= layer < n_layers:
        raise ValueError(
            f"couche {layer} hors bornes : ce modele a {n_layers} couches "
            f"(indices 0-{n_layers - 1}). Le defaut 16 vise le mi-reseau d'un "
            "modele 32 couches ; pour une autre echelle, preferer "
            "--layer-frac 0.5.")
    return {"layer": int(layer),
            "n_layers": int(n_layers),
            "layer_frac": round(layer / (n_layers - 1), 4) if n_layers > 1 else 0.0}


def check_sae_model_match(sae_d_model: int, model_d_model: int,
                          sae_repo: str = "", model: str = "") -> None:
    """Verifie que le SAE encode bien le residual stream de CE modele.

    Remplace un ``assert`` nu : un ``assert`` disparait sous ``python -O`` et
    son message n'indiquait pas quoi corriger. La confusion realiste, une fois
    deux echelles en jeu, est de garder le SAE 9B/W64K (d_model 4096) en
    changeant le modele pour le 2B (d_model 2048) — le produit ``h @ W_enc.T``
    echouerait alors sur une erreur de forme torch illisible.
    """
    if int(sae_d_model) != int(model_d_model):
        raise ValueError(
            f"d_model incompatible : le SAE {sae_repo or '(?)'} encode "
            f"{sae_d_model} dimensions, le modele {model or '(?)'} en produit "
            f"{model_d_model}. Apparier les familles : "
            "Qwen3.5-9B-Base <-> SAE-Res-Qwen3.5-9B-Base-W64K-*, "
            "Qwen3.5-2B(-Base) <-> SAE-Res-Qwen3.5-2B-Base-W32K-*.")


def assert_bf16_readout(quantization_config: object | None,
                        allow_quantized: bool = False) -> None:
    """Refuse une lecture SAE sur un modele charge quantifie.

    Les SAE Qwen-Scope ont ete entraines sur le residual stream **pleine
    precision** du modele *Base*. Lire les features d'un modele post-entraine
    charge en 4-bit et les comparer a une base bf16 produirait un differentiel
    indiscernable de l'erreur d'arrondi de la quantification : le resultat
    aurait l'air d'un effet de post-training alors qu'il mesurerait NF4.

    Le regime correct pour l'arc PT-12 est dissocie : QLoRA (base gelee 4-bit,
    adapters bf16) pour la **boucle d'entrainement**, puis rechargement en
    **bf16** — base + adapters fusionnes — pour la **lecture SAE**.

    ``allow_quantized=True`` reste possible pour une exploration assumee, mais
    doit etre demande explicitement et ecrit dans les metadonnees de la trace.
    """
    if quantization_config is not None and not allow_quantized:
        raise ValueError(
            "modele charge quantifie (quantization_config present) : la "
            "lecture SAE exige bf16. Les SAE sont entraines sur le residual "
            "stream pleine precision, donc un differentiel mesure en 4-bit "
            "melangerait l'effet du post-training et l'erreur d'arrondi NF4. "
            "Recharger base+adapters fusionnes en bf16, ou passer "
            "--allow-quantized-readout pour une exploration assumee.")


# --------------------------------------------------------------------------- #
# Garde-fou cross-L0 (L0_50 <-> L0_100) — etape 2 PT-12 (#10289)
#
# Meme modele, meme d_sae (32 768), mais le top-k officiel du SAE change
# (50 vs 100). Si le script d'extraction encode en top-k=50 sur un SAE
# officiellement L0_100, on perd la moitie des activations et la lecture
# n'est plus comparable a la release officielle — sans erreur, juste une
# mesure degradee. Cette garde refuse systematiquement le desaccord.
# --------------------------------------------------------------------------- #
def assert_sae_topk_compatible(k_sae: int, k_requested: int) -> None:
    """Refuse un encodage top-k qui ne respecte pas le k officiel du SAE.

    Le defaut silencieux que cette fonction ferme : passer ``k=50`` a
    :func:`sae_encode_topk` sur un depot ``L0_100`` ne leve pas d'erreur,
    ``torch.topk`` rend simplement les 50 premieres activations sur 100,
    et tout le reste du pipeline (densification, panel, sortie) tourne
    une mesure **a la moitie de la largeur officielle** — silencieusement,
    sans bandeau, sans garde-fou. C'est exactement le mode de defaillance
    que la note PT-12 de #10289 pointe comme « piege a ne pas rater ».

    La garde impose -- et la garde seule -- que ``k_requested`` egale
    ``k_sae`` (le ``k`` du ``config.json`` du depot SAE). Une exception
    documentee (``--allow-k-override``) est implementee cote CLI dans
    ``extract_sae_traces.py`` pour permettre un encodage non comparable a
    la release (usage recherche explicite uniquement).
    """
    if int(k_sae) != int(k_requested):
        raise ValueError(
            f"top-k incompatible : le SAE est officiellement k={k_sae} (sa "
            f"config.json), la requete est k={k_requested}. Encodage "
            f"silencieusement degrade sinon (top-{k_requested} sur "
            f"top-{k_sae}), sortie non comparable a la release officielle. "
            f"Deux repos distincts sur le meme modele : "
            f"Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50 (k=50) et "
            f"Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_100 (k=100). "
            f"Realigner --k ou --sae-repo et relancer.")


def trace_filename(variant: str, layer: int, *, model: str = "",
                   default_model: str = "", n_layers: int | None = None,
                   n_clamp: int = 0, prefix: str = "ict21_sae") -> str:
    """Nom de fichier de trace **discriminant par echelle**.

    Defaut historique conserve a l'octet pour le modele de reference (les
    traces ``ict21_sae_layer16_{trained,control}.npz`` deja committees et les
    notebooks ICT-21/ICT-24 qui les chargent par chemin explicite continuent de
    fonctionner). Des que le modele differe, un slug d'echelle est insere :
    sans lui, un run 2B et un run 9B a la meme couche 16 ecrivent **le meme
    nom** et le second efface le premier en silence — perte de donnees, pas
    seulement confusion.
    """
    clamp = f"_clamp{n_clamp}" if n_clamp else ""
    if model and default_model and model != default_model:
        slug = model.rstrip("/").split("/")[-1].lower().replace(".", "")
        depth = f"layer{layer}of{n_layers}" if n_layers else f"layer{layer}"
        return f"{prefix}_{slug}_{depth}_{variant}{clamp}.npz"
    return f"{prefix}_layer{layer}_{variant}{clamp}.npz"
