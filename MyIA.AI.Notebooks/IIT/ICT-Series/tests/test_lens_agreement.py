"""Tests de la co-localisation inter-lentilles SAE <-> J-Lens (strate 5, #5681 / #4588). GPU-free.

Couvrent la **glue** ajoutee par :mod:`ict.lens_agreement` (la statistique NN-distance +
null par rotation est deja couverte par ``test_workspace.py`` cote
:func:`ict.workspace.event_colocalization`) :

* :func:`lens_ignition_centers` retrouve les rafales de concentration plantees ;
* :func:`colocalize_lenses` -> ``colocalized`` quand les deux lentilles allument aux
  MEMES positions, ``chance``/``dissociated`` quand elles allument ailleurs ;
* les prompts a ``T`` incompatible sont SAUTES (``n_skipped``) ;
* une lentille qui n'allume jamais donne des prompts ``undefined`` (``n_undefined``) ;
* le module est numpy-only (aucun import torch) ;
* integration : si les traces reelles committees sont presentes, le pilote tourne et
  renvoie un verdict structurellement valide sur les 20 prompts partages.

Les traces synthetiques sont construites dans le format post-``load_traces`` : chaque
lentille a des features "signal" a forte variance inter-jeux (donc selectionnees par
:func:`ict.sae_traces.differential_features`) ; une rafale a la position ``c`` concentre
toute la valeur sur UNE feature signal (Gini eleve, ignition), le reste du temps les
features signal sont equi-actives (Gini ~0, pas d'ignition).
"""

import os
import sys
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import lens_agreement as la  # noqa: E402
from ict.workspace import concentration_series  # noqa: E402
from ict.sae_traces import differential_features  # noqa: E402

# features signal (fort, variance inter-jeux) et fillers (faibles, non differentiels)
SIGNAL = [10, 11, 12, 13, 14, 15]
FILLER = [1, 2, 3]

# Profil de rafale : concentration triangulaire (pic au centre) sur 5 positions.
BURST_PROFILE = [0.5, 0.75, 0.95, 0.75, 0.5]


def _gini_row(L: float, scale: float) -> np.ndarray:
    """Ligne de panel (6 features SIGNAL) dont le Gini vaut EXACTEMENT ``L``.

    Pour un vecteur ``[f, (1-f)/5, ..., (1-f)/5]`` normalise, le Gini (formule de
    :func:`ict.workspace.concentration_series`) vaut ``(6 f - 1) / 5`` ; on inverse
    en ``f = (5 L + 1) / 6`` pour cibler ``L``. Le Gini etant **invariant d'echelle**,
    la mise a l'echelle par jeu (``scale``) donne la variance inter-jeux qui fait
    selectionner ces features par :func:`differential_features` SANS toucher la
    concentration.
    """
    F = len(SIGNAL)
    f = (5.0 * L + 1.0) / 6.0
    row = np.full(F, (1.0 - f) / (F - 1), dtype=np.float64)
    row[0] = f
    return row * scale


def _build_traces(
    bursts: Dict[Tuple[str, int], List[int]],
    *,
    T: int = 120,
    sets=("setA", "setB"),
    n_prompts: int = 2,
    d_sae: int = 64,
    seed: int = 0,
) -> dict:
    """Traces synthetiques (format post-load) avec rafales de concentration plantees.

    ``bursts`` : centres de rafale (profil :data:`BURST_PROFILE`, 5 positions de large,
    pic au centre) par prompt. Hors rafale, la concentration **alterne** bas/moyen-bas
    (0.02 / 0.06) : cette alternance garantit qu'AUCUNE fenetre baseline de longueur
    ``persistence=3`` ne franchit le quantile 0.9 (les positions "hautes" sont isolees,
    espacees de 1), donc une lentille sans rafale ne produit **aucune** ignition. A une
    rafale, la concentration monte franchement (jusqu'a 0.95) sur >= 3 positions
    contigues -> une ignition centree sur le pic. Le seuil interne ``quantile(conc, q)``
    de :func:`lens_ignition_centers` separe ainsi proprement rafales et baseline.

    La concentration ciblee est realisee via :func:`_gini_row` (Gini exact, invariant
    d'echelle) ; la mise a l'echelle ``1 + si`` par jeu porte la variance inter-jeux qui
    fait selectionner les features signal par :func:`differential_features`.
    """
    rng = np.random.default_rng(seed)
    F = len(SIGNAL)
    K = F + len(FILLER)
    prompts: Dict[Tuple[str, int], dict] = {}
    for si, s in enumerate(sets):
        scale = 1.0 + si                          # variance inter-jeux -> signal selectionne
        for i in range(n_prompts):
            ids = np.zeros((T, K), dtype=np.int32)
            vals = np.zeros((T, K), dtype=np.float32)
            ids[:, :F] = SIGNAL
            ids[:, F:] = FILLER
            # baseline : concentration alternee basse (aucun run de 3 au-dessus du q0.9)
            for t in range(T):
                L = 0.02 if t % 2 == 0 else 0.06
                vals[t, :F] = _gini_row(L, scale)
            # rafales : profil triangulaire (pic au centre) sur 5 positions
            for c in bursts.get((s, i), []):
                for off, L in zip(range(-2, 3), BURST_PROFILE):
                    t = c + off
                    if 0 <= t < T:
                        vals[t, :F] = _gini_row(L, scale)
            # fillers : faibles, quasi constants (variance inter-jeux ~0 -> non selectionnes)
            vals[:, F:] = 0.01 + rng.uniform(0, 1e-4, size=(T, K - F)).astype(np.float32)
            prompts[(s, i)] = {
                "ids": ids,
                "vals": vals,
                "tokens": np.array([f"t{t}" for t in range(T)], dtype=str),
            }
    return {"meta": {"d_sae": d_sae, "k": K, "layer": 16, "variant": "synthetic"},
            "prompts": prompts}


# --------------------------------------------------------------------------- #
# lens_ignition_centers
# --------------------------------------------------------------------------- #
def test_lens_ignition_centers_finds_planted_bursts():
    """Les centres d'ignition tombent pres des rafales plantees."""
    tr = _build_traces({("setA", 0): [30, 80]}, T=120)
    feats = differential_features(tr, k=6)
    centers = la.lens_ignition_centers(tr, feats, q=0.9, persistence=3)
    got = centers[("setA", 0)]
    ev_centers, T = got
    assert T == 120
    assert len(ev_centers) == 2, ev_centers
    assert any(abs(c - 30) <= 2 for c in ev_centers), ev_centers
    assert any(abs(c - 80) <= 2 for c in ev_centers), ev_centers


def test_lens_ignition_centers_empty_without_bursts():
    """Sans rafale (concentration plate) : aucun centre d'ignition."""
    tr = _build_traces({}, T=100)                 # aucune rafale nulle part
    feats = differential_features(tr, k=6)
    centers = la.lens_ignition_centers(tr, feats, q=0.9, persistence=3)
    assert all(len(c) == 0 for c, _ in centers.values())


# --------------------------------------------------------------------------- #
# colocalize_lenses -- verdicts
# --------------------------------------------------------------------------- #
def _both_lens(bursts_a, bursts_b, **kw):
    a = _build_traces(bursts_a, seed=0, **kw)
    b = _build_traces(bursts_b, seed=1, **kw)     # bruit filler distinct : lentilles differentes
    return a, b


def test_colocalize_lenses_same_positions_is_colocalized():
    """Deux lentilles allumant aux MEMES positions -> verdict agrege 'colocalized'."""
    pos = {("setA", 0): [15, 55, 95], ("setA", 1): [20, 60, 100],
           ("setB", 0): [15, 55, 95], ("setB", 1): [20, 60, 100]}
    a, b = _both_lens(pos, pos, T=120)
    r = la.colocalize_lenses(a, b, k=6, q=0.9, persistence=3, n_null=200,
                             rng=np.random.default_rng(0))
    assert r["n_prompts"] == 4
    assert r["n_skipped"] == 0
    assert r["verdict"] == "colocalized", r
    assert r["n_colocalized"] > r["n_dissociated"]
    assert r["z_mean"] > 0


def test_colocalize_lenses_different_positions_not_colocalized():
    """Deux lentilles allumant a des positions decalees -> PAS 'colocalized'."""
    pos_a = {("setA", 0): [15, 55, 95], ("setA", 1): [15, 55, 95],
             ("setB", 0): [15, 55, 95], ("setB", 1): [15, 55, 95]}
    pos_b = {("setA", 0): [35, 75, 110], ("setA", 1): [35, 75, 110],
             ("setB", 0): [35, 75, 110], ("setB", 1): [35, 75, 110]}
    a, b = _both_lens(pos_a, pos_b, T=120)
    r = la.colocalize_lenses(a, b, k=6, q=0.9, persistence=3, n_null=200,
                             rng=np.random.default_rng(0))
    assert r["n_prompts"] == 4
    assert r["verdict"] != "colocalized", r


def test_colocalize_lenses_skips_length_mismatch():
    """Un prompt a T different entre les deux lentilles est saute (n_skipped)."""
    pos = {("setA", 0): [20, 60], ("setA", 1): [20, 60],
           ("setB", 0): [20, 60], ("setB", 1): [20, 60]}
    a, b = _both_lens(pos, pos, T=120)
    # tronque un prompt de la lentille B a T=90
    key = ("setA", 0)
    b["prompts"][key]["ids"] = b["prompts"][key]["ids"][:90]
    b["prompts"][key]["vals"] = b["prompts"][key]["vals"][:90]
    b["prompts"][key]["tokens"] = b["prompts"][key]["tokens"][:90]
    r = la.colocalize_lenses(a, b, k=6, q=0.9, persistence=3, n_null=100,
                             rng=np.random.default_rng(0))
    assert r["n_skipped"] == 1
    assert any(s["prompt"] == key for s in r["skipped"])
    assert r["n_prompts"] == 3


def test_colocalize_lenses_undefined_when_a_lens_never_ignites():
    """Une lentille sans rafale -> prompts 'undefined' (comptes, exclus des z)."""
    pos_a = {("setA", 0): [20, 60], ("setA", 1): [20, 60],
             ("setB", 0): [20, 60], ("setB", 1): [20, 60]}
    a, b = _both_lens(pos_a, {}, T=120)           # lentille B : aucune ignition
    r = la.colocalize_lenses(a, b, k=6, q=0.9, persistence=3, n_null=100,
                             rng=np.random.default_rng(0))
    assert r["n_undefined"] == 4
    assert r["n_colocalized"] == 0
    assert r["verdict"] == "chance"               # ni coloc ni disso -> chance
    assert np.isnan(r["z_mean"])


def test_colocalize_lenses_reproducible_with_seed():
    """Meme graine -> meme verdict agrege et memes comptes."""
    pos = {("setA", 0): [15, 55, 95], ("setA", 1): [20, 60, 100],
           ("setB", 0): [15, 55, 95], ("setB", 1): [20, 60, 100]}
    a, b = _both_lens(pos, pos, T=120)
    r1 = la.colocalize_lenses(a, b, k=6, n_null=200, rng=np.random.default_rng(3))
    r2 = la.colocalize_lenses(a, b, k=6, n_null=200, rng=np.random.default_rng(3))
    assert r1["verdict"] == r2["verdict"]
    assert r1["n_colocalized"] == r2["n_colocalized"]
    assert r1["z_mean"] == r2["z_mean"] or (np.isnan(r1["z_mean"]) and np.isnan(r2["z_mean"]))


# --------------------------------------------------------------------------- #
# Architecture
# --------------------------------------------------------------------------- #
def test_lens_agreement_module_is_numpy_only():
    """Aucune INSTRUCTION d'import torch (le GPU reste confine aux scripts d'extraction).

    Verification par ligne (et non par sous-chaine) : la prose de la docstring peut
    legitimement contenir les mots ``import torch`` (« aucun import torch ») sans que
    le module importe torch. Seule une *instruction* ``import torch`` / ``from torch ...``
    est proscrite.
    """
    src = Path(la.__file__).read_text(encoding="utf-8")
    import_lines = [ln.strip() for ln in src.splitlines()]
    assert not any(ln.startswith("import torch") for ln in import_lines)
    assert not any(ln.startswith("from torch") for ln in import_lines)


# --------------------------------------------------------------------------- #
# Integration : traces reelles committees (si presentes)
# --------------------------------------------------------------------------- #
REAL = Path(__file__).parent.parent / "traces"


def test_real_fixtures_colocalization_runs():
    """Sur les traces reelles (si presentes) : le pilote tourne, verdict valide sur 20 prompts."""
    sae_p = REAL / "ict21_sae_layer16_trained.npz"
    jl_p = REAL / "ict24_jlens_layer16_trained.npz"
    if not (sae_p.exists() and jl_p.exists()):
        pytest.skip("traces reelles absentes (extraction GPU non committee ici)")
    from ict import sae_traces, jlens_traces

    sae = sae_traces.load_traces(sae_p)
    jl = jlens_traces.load_traces(jl_p)
    r = la.colocalize_lenses(sae, jl, k=64, q=0.9, persistence=3, n_null=200,
                             rng=np.random.default_rng(0))
    assert r["n_prompts"] == 20                    # 5 jeux x 4 prompts, T-alignes
    assert r["n_skipped"] == 0
    assert r["verdict"] in {"colocalized", "dissociated", "chance"}
    # chaque verdict par prompt est bien structure
    for p in r["per_prompt"]:
        assert set(p) >= {"prompt", "verdict", "obs", "z", "n_ign_a", "n_ign_b"}
        assert p["verdict"] in {"colocalized", "dissociated", "chance", "undefined"}
