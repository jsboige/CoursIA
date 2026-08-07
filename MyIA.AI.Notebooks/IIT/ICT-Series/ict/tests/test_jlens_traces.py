"""Tests unitaires pour ``ict.jlens_traces`` (Track S tete-a-tete SAE<->J, Epic #5681).

Le module :mod:`ict.jlens_traces` est le **miroir J-Lens** de :mod:`ict.sae_traces`
pour la piste Track S du tete-a-tete SAE/J-Lens d'ICT-24 (strate 5, Epic #4588).
Meme schema ``.npz``, mais avec un **garde-fou anti-melange** : la trace doit
porter ``meta["lens"] == "jacobian"`` (ou absent, retro-compat), et toute trace
``meta["lens"] == "sae"`` est REJETEE par ``load_traces`` -- un test faux-positif
qui chargerait une trace SAE dans le notebook J-Lens casserait la co-location
cross-methode de #5681.

Le module reexporte par ailleurs 6 fonctions d'aval de :mod:`ict.sae_traces`
(densify, mean_activation_by_set, differential_features, acts_topk_panels,
binarize_quantile, states_from_panel). Ces fonctions sont referencees par
``__all__`` mais ne sont PAS redefinies localement -- c'est l'invariant
methodologique DRY (un meme appareil sur les deux familles). Les tests
suivants attestent chaque contrat :

    1.  (``__all__``) : la liste ``__all__`` expose exactement 7 noms : la
        ``load_traces`` propre + 6 reexports ``sae_traces``.
    2.  (DRY reexports) : les 6 noms reexportes designent **la meme fonction**
        que dans :mod:`ict.sae_traces` (identity, pas alias local) -- invariant
        DRY du tete-a-tete cross-methode.
    3.  (accept jacobian) : ``load_traces`` accepte une trace avec
        ``meta["lens"] == "jacobian"`` (cas nominal de la piste Track S).
    4.  (accept absent)  : ``load_traces`` accepte une trace sans champ
        ``meta["lens"]`` (retro-compatibilite avec un extracteur qui n'ecrit
        pas encore le marqueur, cf. docstring L110-113).
    5.  (refuse sae)     : ``load_traces`` REFUSE avec ``ValueError`` une
        trace ``meta["lens"] == "sae"`` -- c'est une trace SAE, pas
        J-Lens ; le notebook doit utiliser :func:`ict.sae_traces.load_traces`
        pour cette trace (garde-fou anti-melange).
    6.  (structure aval) : la sortie de ``load_traces`` suit le meme schema
        ``{"meta": dict, "prompts": {(set_name, i): {"ids", "vals",
        "tokens"}}}`` que :func:`ict.sae_traces.load_traces`, pour que les
        fonctions d'aval reexportees (densify, ...) restent interchangeables.
    7.  (densify reel)    : le reexport ``densify`` materialise un panneau
        dense [T, F] a partir de sparse ``ids``/``vals`` -- on verifie le
        contrat fonctionnel exact (feature absente du top-k = activation 0,
        feature presente = activation fidele), anti-regression d'un futur
        stub silencieux.
    8.  (E2E mini)        : ``load_traces`` accepte une trace J-Lens nominale
        (jacobian + 1 prompt complet T=4, k=3, d_sae=5) et ``densify`` produit
        le panneau attendu -- sanity end-to-end du pipeline Track S.

Implementation : aucune dependance externe ; un seul import numpy + import du
package ``ict``. Les seuils (``k=3``, ``d_sae=5``, ``T=4``) sont des fixtures
internes -- les tests ne FORCENT aucun verdict sur les resultats
``workspace``, ``synthesis`` ou ``lens_agreement``, ils verifient la
**COHERENCE** des invariants structurels du module.
"""

from __future__ import annotations

import os
import sys

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import json

import numpy as np
import pytest

from ict import jlens_traces as jl
from ict import sae_traces as sae


# --------------------------------------------------------------------------- #
#  Helpers : fabrication de traces J-Lens synthetiques (.npz-like en memoire) #
# --------------------------------------------------------------------------- #


class _InMemoryNpz:
    """Emule un ``np.load(path).files`` + ``data[key]`` pour les tests.

    Le format reel (.npz) est un zip multi-tableaux ; ici on enregistre
    directement les arrays dans un dict ``files`` + un acces indexe par
    cle compatible avec le parsing ``(set, idx, field)`` de
    :func:`ict.sae_traces.load_traces`.
    """

    def __init__(self, meta: dict, arrays: dict[str, np.ndarray]):
        self._files = ["__meta__"] + list(arrays.keys())
        self._arrays = dict(arrays)
        self._arrays["__meta__"] = json.dumps(meta)

    def __iter__(self):
        return iter(self._files)

    @property
    def files(self):
        return list(self._files)

    def __getitem__(self, key: str):
        return self._arrays[key]


def _make_trace_npz(
    meta: dict,
    prompts: dict[tuple[str, int], dict],
) -> _InMemoryNpz:
    """Construit un ``_InMemoryNpz`` a partir d'un meta + prompts.

    Suit le schema ``<set>__<idx>__<field>`` (cf. ``sae_traces.load_traces``).
    """
    arrays: dict[str, np.ndarray] = {}
    for (set_name, idx), entry in prompts.items():
        for field in ("topk_ids", "topk_vals", "tokens"):
            if field == "tokens":
                arrays[f"{set_name}__{idx}__{field}"] = np.array(entry[field])
            else:
                arrays[f"{set_name}__{idx}__{field}"] = np.asarray(entry[field])
    return _InMemoryNpz(meta=meta, arrays=arrays)


def _fake_load_factory(npz_obj: _InMemoryNpz):
    """Retourne un patch compatible avec le binding local
    ``ict.jlens_traces._sae_load_traces``.

    Le module ``jlens_traces`` importe
    ``from .sae_traces import load_traces as _sae_load_traces`` (binding
    local). Le monkeypatch doit viser ``ict.jlens_traces._sae_load_traces``
    (le module qui APPELLE), pas ``ict.sae_traces.load_traces`` (la
    source) -- un monkeypatch sur la source ne prend pas effet sur le
    binding local (import copy).
    """

    def fake_load_traces(path):  # noqa: ARG001
        return {"meta": json.loads(npz_obj["__meta__"]), "prompts": _parse_prompts(npz_obj)}

    return fake_load_traces


def _parse_prompts(npz_obj: _InMemoryNpz) -> dict[tuple[str, int], dict]:
    """Reconstruit le dict ``prompts`` depuis les cles ``<set>__<idx>__<field>``."""
    out: dict[tuple[str, int], dict] = {}
    for key in npz_obj.files:
        if key == "__meta__":
            continue
        set_name, idx, field = key.rsplit("__", 2)
        entry = out.setdefault((set_name, int(idx)), {})
        if field == "topk_ids":
            entry["ids"] = npz_obj[key].astype(np.int32)
        elif field == "topk_vals":
            entry["vals"] = npz_obj[key].astype(np.float32)
        elif field == "tokens":
            entry["tokens"] = npz_obj[key]
    return out


# --------------------------------------------------------------------------- #
#  Gate 1 : __all__ expose 7 noms (load_traces + 6 reexports sae_traces)     #
# --------------------------------------------------------------------------- #


def test_all_exposes_load_traces_and_six_reexports():
    """``__all__`` contient exactement 7 noms : ``load_traces`` + 6
    fonctions reexportees depuis :mod:`ict.sae_traces`.

    Anti-regression : si quelqu'un redefinit localement une fonction
    d'aval (au lieu de la reexporter) ou si un futur auteur retire
    par megarde un nom, ce test attrape la deviation a l'import.
    """
    expected = {
        "load_traces",
        "densify",
        "mean_activation_by_set",
        "differential_features",
        "acts_topk_panels",
        "binarize_quantile",
        "states_from_panel",
    }
    assert set(jl.__all__) == expected, (
        f"__all__ attendu = {expected}, recu = {set(jl.__all__)}"
    )


# --------------------------------------------------------------------------- #
#  Gate 2 : DRY invariant -- les 6 reexports designent la MEME fonction      #
# --------------------------------------------------------------------------- #


def test_reexports_are_identical_to_sae_traces_functions():
    """Les 6 noms reexportes sont **la meme fonction** que dans
    :mod:`ict.sae_traces` -- c'est l'invariant DRY du tete-a-tete
    cross-methode : un meme appareil sur SAE et J-Lens, pas deux
    implementations paralleles qui deriveraient.

    Le test verifie ``is`` (identity), pas seulement ``==``.
    """
    pairs = [
        ("densify", sae.densify),
        ("mean_activation_by_set", sae.mean_activation_by_set),
        ("differential_features", sae.differential_features),
        ("acts_topk_panels", sae.acts_topk_panels),
        ("binarize_quantile", sae.binarize_quantile),
        ("states_from_panel", sae.states_from_panel),
    ]
    for name, expected_fn in pairs:
        got = getattr(jl, name)
        assert got is expected_fn, (
            f"jl.{name} devrait etre is sae.{name} (DRY), "
            f"mais recu {got!r} (possible stub local ?)"
        )


# --------------------------------------------------------------------------- #
#  Gate 3 : load_traces accepte meta['lens'] == 'jacobian' (cas nominal)     #
# --------------------------------------------------------------------------- #


def test_load_traces_accepts_jacobian_lens(monkeypatch):
    """Cas nominal de la piste Track S : ``meta['lens'] == 'jacobian'``.

    La trace est chargee par delegation a :func:`ict.sae_traces.load_traces`,
    puis le garde-fou anti-melange verifie que la trace est bien J-Lens
    (et pas SAE par megarde).
    """
    npz = _make_trace_npz(
        meta={"lens": "jacobian", "d_sae": 4, "k": 2, "layer": 16, "variant": "9B-Base"},
        prompts={
            ("setA", 0): {
                "topk_ids": [[0, 1], [2, 3]],
                "topk_vals": [[1.0, 0.5], [0.8, 0.2]],
                "tokens": ["a", "b"],
            }
        },
    )
    monkeypatch.setattr(jl, "_sae_load_traces", _fake_load_factory(npz))

    out = jl.load_traces("ignored_path.npz")
    assert out["meta"]["lens"] == "jacobian"
    assert ("setA", 0) in out["prompts"]


# --------------------------------------------------------------------------- #
#  Gate 4 : load_traces accepte trace SANS meta['lens'] (retro-compat)        #
# --------------------------------------------------------------------------- #


def test_load_traces_accepts_missing_lens_field(monkeypatch):
    """Retro-compatibilite avec un extracteur qui n'ecrit pas encore
    ``meta['lens']`` (cf. docstring L110-113 de jlens_traces).

    Le garde-fou NE DOIT PAS casser l'execution si le champ est absent
    -- il reserve le refus uniquement aux cas ``meta['lens'] == 'sae'``
    (mauvais pipeline). L'absence = ``accept`` par defaut.
    """
    npz = _make_trace_npz(
        meta={"d_sae": 4, "k": 2, "layer": 16},  # pas de 'lens'
        prompts={
            ("setA", 0): {
                "topk_ids": [[0, 1]],
                "topk_vals": [[1.0, 0.5]],
                "tokens": ["a"],
            }
        },
    )
    monkeypatch.setattr(jl, "_sae_load_traces", _fake_load_factory(npz))

    out = jl.load_traces("legacy_trace.npz")
    assert "lens" not in out["meta"]  # preserve le meta original
    assert ("setA", 0) in out["prompts"]


# --------------------------------------------------------------------------- #
#  Gate 5 : load_traces REFUSE meta['lens'] == 'sae' (garde-fou anti-melange) #
# --------------------------------------------------------------------------- #


def test_load_traces_refuses_sae_lens_with_value_error(monkeypatch):
    """Garde-fou anti-melange : si la trace porte
    ``meta['lens'] == 'sae'``, c'est une trace SAE, pas J-Lens. Le
    notebook doit utiliser :func:`ict.sae_traces.load_traces` pour cette
    trace -- la laisser passer dans le notebook J-Lens casserait la
    co-localisation cross-methode de #5681 Track S.

    Le test verifie que ``ValueError`` est leve, et que le message
    mentionne la destination correcte (``ict.sae_traces``).
    """
    npz = _make_trace_npz(
        meta={"lens": "sae", "d_sae": 4, "k": 2, "layer": 16, "variant": "Qwen-Scope"},
        prompts={
            ("setA", 0): {
                "topk_ids": [[0, 1]],
                "topk_vals": [[1.0, 0.5]],
                "tokens": ["a"],
            }
        },
    )
    monkeypatch.setattr(jl, "_sae_load_traces", _fake_load_factory(npz))

    with pytest.raises(ValueError) as excinfo:
        jl.load_traces("sae_trace_mislabeled.npz")
    msg = str(excinfo.value)
    assert "sae" in msg.lower(), f"message doit mentionner 'sae' : recu {msg!r}"
    assert "sae_traces" in msg, (
        f"message doit rediriger vers ict.sae_traces.load_traces : recu {msg!r}"
    )


# --------------------------------------------------------------------------- #
#  Gate 6 : structure aval compatible avec les fonctions d'aval reexportees  #
# --------------------------------------------------------------------------- #


def test_load_traces_returns_schema_compatible_with_reexports(monkeypatch):
    """La sortie ``{"meta", "prompts"}`` de :func:`jl.load_traces` est
    compatible avec les fonctions d'aval reexportees (``densify``,
    ``mean_activation_by_set``, etc.) : chaque prompt a ``{"ids",
    "vals"}`` (et eventuellement ``"tokens"``), types numpy corrects.

    On verifie un aller-retour : on charge via ``jl.load_traces``,
    puis on appelle ``jl.densify`` sur le prompt -- les types et shapes
    sont coherents (pas de ``KeyError`` ni de cast surprise).
    """
    T, k = 3, 2
    npz = _make_trace_npz(
        meta={"lens": "jacobian", "d_sae": 4, "k": k},
        prompts={
            ("setA", 0): {
                "topk_ids": np.arange(T * k, dtype=np.int32).reshape(T, k),
                "topk_vals": np.ones((T, k), dtype=np.float32) * 0.5,
                "tokens": np.array(["x", "y", "z"]),
            }
        },
    )
    monkeypatch.setattr(jl, "_sae_load_traces", _fake_load_factory(npz))

    out = jl.load_traces("trace.npz")
    entry = out["prompts"][("setA", 0)]
    assert entry["ids"].dtype == np.int32
    assert entry["vals"].dtype == np.float32
    assert entry["ids"].shape == (T, k)
    assert entry["vals"].shape == (T, k)

    # densify via le reexport -- doit fonctionner sans surprise.
    feature_ids = np.array([0, 2, 4], dtype=np.int64)  # 5 -> hors top-k
    dense = jl.densify(entry["ids"], entry["vals"], feature_ids)
    assert dense.shape == (T, len(feature_ids))


# --------------------------------------------------------------------------- #
#  Gate 7 : densify reel -- sparse -> dense avec zeros structurels exacts     #
# --------------------------------------------------------------------------- #


def test_densify_reexport_is_functional_not_stub():
    """Anti-regression : le reexport ``jl.densify`` est fonctionnel, pas
    un stub silencieux. On verifie le contrat fonctionnel exact :

    * une feature ABSENTE du top-k a activation **exactement 0** (zeros
      structurels du SAE top-k, et approximation rang-k du J-Lens) ;
    * une feature PRESENTE dans le top-k a activation fidele a ``vals``.

    Si quelqu'un remplacait le reexport par un stub local (genre
    ``return np.zeros_like(...)``), ce test attraperait la deviation.
    """
    # Top-k = [10, 20] avec vals [1.0, 0.5] ; feature_ids cibles [10, 20, 30]
    ids = np.array([[10, 20]], dtype=np.int32)
    vals = np.array([[1.0, 0.5]], dtype=np.float32)
    feature_ids = np.array([10, 20, 30], dtype=np.int64)

    dense = jl.densify(ids, vals, feature_ids)
    assert dense.shape == (1, 3)
    # Ligne 0 : feature 10 active a 1.0, 20 active a 0.5, 30 absente -> 0.
    assert np.isclose(dense[0, 0], 1.0)
    assert np.isclose(dense[0, 1], 0.5)
    assert dense[0, 2] == 0.0


# --------------------------------------------------------------------------- #
#  Gate 8 : E2E mini -- jacobian + 1 prompt complet -> densify -> panneau    #
# --------------------------------------------------------------------------- #


def test_e2e_minimal_jacobian_trace_roundtrip(monkeypatch):
    """Sanity end-to-end du pipeline Track S : on fabrique une trace
    J-Lens nominale (1 set, 1 prompt, T=4, k=3, d_sae=5), on la charge
    via :func:`jl.load_traces`, on densifie via :func:`jl.densify`,
    et on verifie que le panneau dense [T, F] est conforme aux
    ``vals`` du sparse.
    """
    T, k, d_sae = 4, 3, 5
    # ids dans [0, d_sae) ; vals >= 0 ; exactement T*k valeurs par ligne.
    ids = np.array(
        [[0, 2, 4], [1, 3, 4], [0, 1, 2], [3, 4, 0]], dtype=np.int32
    )
    vals = np.array(
        [[1.0, 0.8, 0.6], [0.7, 0.5, 0.9], [0.4, 0.3, 0.2], [1.0, 0.5, 0.5]],
        dtype=np.float32,
    )
    npz = _make_trace_npz(
        meta={"lens": "jacobian", "d_sae": d_sae, "k": k, "layer": 16, "variant": "9B-Base"},
        prompts={
            ("setA", 0): {
                "topk_ids": ids,
                "topk_vals": vals,
                "tokens": np.array(["t0", "t1", "t2", "t3"]),
            }
        },
    )
    monkeypatch.setattr(jl, "_sae_load_traces", _fake_load_factory(npz))

    # Charge la trace via le module J-Lens (doit accepter "jacobian").
    out = jl.load_traces("e2e_trace.npz")
    assert out["meta"]["lens"] == "jacobian"
    assert out["meta"]["d_sae"] == d_sae

    entry = out["prompts"][("setA", 0)]
    # Densifie sur les 5 features completes ; le panneau doit etre [T, d_sae].
    feature_ids = np.arange(d_sae, dtype=np.int64)
    dense = jl.densify(entry["ids"], entry["vals"], feature_ids)
    assert dense.shape == (T, d_sae)

    # Verif ponctuelle : token 0, feature 0 = 1.0 ; token 0, feature 1 absente -> 0.
    assert np.isclose(dense[0, 0], 1.0)
    assert dense[0, 1] == 0.0
    # Token 3, feature 4 = 0.5 ; token 3, feature 2 absente -> 0.
    assert np.isclose(dense[3, 4], 0.5)
    assert dense[3, 2] == 0.0
