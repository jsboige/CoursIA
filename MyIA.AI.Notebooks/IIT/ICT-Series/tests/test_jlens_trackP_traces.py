"""Tests de l'adaptateur de traces J-Lens Track P (ICT-24, #5681). GPU-free.

Couvrent :
* le round-trip ``.npz`` -> :func:`ict.jlens_trackP_traces.load_traces` (sans pickle) ;
* le **garde-fou anti-mélange** du tete-a-tete #5681 Track P :
  - une trace portant ``meta["lens"] == "sae"`` est REFUSEE,
  - une fixture Track S (``meta["track"]`` commence par "S") est REFUSEE (modèle 9B,
    pas comparable au 4B persona),
  - une fixture Track P (``track`` commence par "P") ou sans champ ``track``/``lens``
    est acceptee ;
* la selection differentielle reutilisee de :mod:`ict.sae_traces` (fonctions
  ``densify`` / ``differential_features`` / ``acts_topk_panels`` /
  ``binarize_quantile`` / ``states_from_panel``) tournent a l'identique ;
* **acceptance #2 de #5681** : le pipeline aval :mod:`ict.workspace` (batterie
  d'emergence) tourne **inchange** sur des traces J-lens Track P (persona), via
  l'adaptateur -- un test end-to-end plante une ignition temporelle dans un prompt
  persona et verifie sa detection + le deroulement de la batterie ;
* si les traces reelles Track P etaient committes (extraction GPU2), un test
  d'integration verifierait leur schema (skip tant que la piste GPU2 de #5681
  Track P n'est pas livree).
"""

import json
import os
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import jlens_trackP_traces as jtp  # noqa: E402
from ict import workspace  # noqa: E402  (acceptance #2 : aval inchange)
from ict import sae_traces as st  # noqa: E402  (anti-melange : on refuse ses traces)
from ict import jlens_traces as jt_s  # noqa: E402  (anti-melange : on refuse Track S)

D_JLENS = 2000          # dimension du J-space (nom de champ ``d_sae`` herite du schema commun)
K_TOPK = 50             # top-k des directions J gardees par token (troncature rang-k)
T = 120


# --------------------------------------------------------------------------- #
# Fixture : npz synthetique J-Lens Track P avec structure differentielle plantee
# --------------------------------------------------------------------------- #
def _write_npz(path, meta_lens="jacobian", meta_track="P (persona)"):
    """Deux personas x deux prompts. Feature 7 active seulement dans le persona A
    (differentielle), feature 2 partout (non differentielle). Le prompt
    (``persona_cautious``, 0) porte en plus une **ignition temporelle plantee** :
    sa seconde moitie est fortement concentree sur la feature 7 (Gini eleve)."""
    rng = np.random.default_rng(0)
    arrays = {}
    for set_name, planted, val in (("persona_cautious", 7, 5.0),
                                   ("persona_enthusiastic", 13, 4.0)):
        for i in range(2):
            ids = rng.integers(20, D_JLENS, size=(T, K_TOPK)).astype(np.int32)
            vals = rng.uniform(0.05, 0.3, size=(T, K_TOPK)).astype(np.float16)
            ids[:, 0] = 2                      # ubiquitaire, non differentielle
            vals[:, 0] = 10.0
            ids[:, 1] = planted                # discriminante du persona
            vals[:, 1] = val
            if set_name == "persona_cautious" and i == 0:
                # ignition temporelle : 2e moitie fortement concentree sur feat 7.
                half = T // 2
                ids[half:, 0] = 7
                vals[half:, 0] = 8.0
                ids[half:, 1] = 1500            # id neutre hors du panel differentiel
                vals[half:, 1] = 0.05
                vals[half:, 2:] = 0.05          # ecrase le reste -> Gini ~ 1
            arrays[f"{set_name}__{i}__topk_ids"] = ids
            arrays[f"{set_name}__{i}__topk_vals"] = vals
            arrays[f"{set_name}__{i}__tokens"] = np.array(
                [f"tok{t}" for t in range(T)], dtype=str)
    meta = {"d_sae": D_JLENS, "k": K_TOPK, "layer": 16, "variant": "synthetic"}
    if meta_lens is not None:
        meta["lens"] = meta_lens
    if meta_track is not None:
        meta["track"] = meta_track
    arrays["__meta__"] = np.array(json.dumps(meta))
    np.savez_compressed(path, **arrays)


@pytest.fixture()
def trackP_npz(tmp_path):
    path = tmp_path / "trackP.npz"
    _write_npz(path)
    return path


# --------------------------------------------------------------------------- #
# Round-trip + garde-fou anti-melange (apport specifique de jlens_trackP_traces)
# --------------------------------------------------------------------------- #
def test_load_traces_roundtrip(trackP_npz):
    tr = jtp.load_traces(trackP_npz)
    assert tr["meta"]["d_sae"] == D_JLENS
    assert tr["meta"]["lens"] == "jacobian"
    assert tr["meta"]["track"].startswith("P")
    assert set(tr["prompts"]) == {("persona_cautious", 0), ("persona_cautious", 1),
                                  ("persona_enthusiastic", 0), ("persona_enthusiastic", 1)}
    e = tr["prompts"][("persona_cautious", 0)]
    assert e["ids"].shape == (T, K_TOPK) and e["ids"].dtype == np.int32
    assert e["vals"].shape == (T, K_TOPK) and e["vals"].dtype == np.float32
    assert e["tokens"].shape == (T,)


def test_load_traces_accepts_missing_track_and_lens(tmp_path):
    """Retro-compatibilite : un extracteur qui n'écrit ni ``track`` ni ``lens`` est accepte."""
    path = tmp_path / "bare.npz"
    _write_npz(path, meta_lens=None, meta_track=None)
    tr = jtp.load_traces(path)
    assert "lens" not in tr["meta"]
    assert "track" not in tr["meta"]


def test_load_traces_rejects_sae_trace(tmp_path):
    """Garde-fou anti-melange #5681 : une trace SAE (lens='sae') est REFUSEE."""
    path = tmp_path / "sae_mislabelled.npz"
    _write_npz(path, meta_lens="sae")
    with pytest.raises(ValueError, match="sae"):
        jtp.load_traces(path)


def test_load_traces_rejects_trackS_fixture(tmp_path):
    """Garde-fou anti-melange Track S/Track P : une fixture Track S (9B-Base,
    structure) est REFUSEE par le loader Track P (modèle 4B persona, non comparable)."""
    path = tmp_path / "trackS_fixture.npz"
    _write_npz(path, meta_track="S (base, structure -- pas persona)")
    with pytest.raises(ValueError, match="Track S"):
        jtp.load_traces(path)


def test_trackP_accepted_by_own_loader_but_trackS_loader_also_loads(trackP_npz):
    """La fixture Track P passe SON loader. Le loader Track S (jt_s) ne filtre PAS
    le champ track -> il l'accepterait aussi (pas son rôle de filtrer Track P).
    L'anti-melange est asymétrique par construction : chaque loader protège SON
    notebook (Track P refuse Track S ; Track S refuse SAE). On vérifie ici la
    symétrie utile : le loader Track P refuse bien une fixture Track S
    (test_load_traces_rejects_trackS_fixture) ET une SAE (test ci-dessus)."""
    tr = jtp.load_traces(trackP_npz)
    assert tr["meta"]["track"].startswith("P")


# --------------------------------------------------------------------------- #
# Fonctions d'aval reexportees de sae_traces (memes invariants)
# --------------------------------------------------------------------------- #
def test_differential_features_finds_planted(trackP_npz):
    tr = jtp.load_traces(trackP_npz)
    top = set(jtp.differential_features(tr, k=2).tolist())
    assert top == {7, 13}, top                  # plantees, pas l'ubiquitaire 2


def test_densify_and_panels(trackP_npz):
    tr = jtp.load_traces(trackP_npz)
    e = tr["prompts"][("persona_enthusiastic", 1)]
    feats = np.array([13, 2, D_JLENS + 500])   # plantee, ubiquitaire, hors-range
    dense = jtp.densify(e["ids"], e["vals"], feats)
    assert dense.shape == (T, 3)
    assert np.allclose(dense[:, 0], e["vals"][:, 1])     # feat 13 en col 0
    assert np.all(dense[:, 2] == 0.0)                    # hors-range => jamais vue => 0
    feats = jtp.differential_features(tr, k=4)
    panels = jtp.acts_topk_panels(tr, feats)
    assert set(panels) == set(tr["prompts"])
    assert all(p.shape == (T, 4) for p in panels.values())


def test_binarize_states_guards():
    dense = np.zeros((10, 2), dtype=np.float32)
    dense[:5, 0] = [1, 2, 3, 4, 5]
    bits = jtp.binarize_quantile(dense, q=0.5)
    assert bits[:, 1].sum() == 0                 # jamais active -> False
    with pytest.raises(ValueError):
        jtp.binarize_quantile(dense, q=1.0)
    states = jtp.states_from_panel(np.array([[0, 0], [1, 0], [0, 1]], dtype=bool))
    assert states.tolist() == [0, 1, 2]
    with pytest.raises(ValueError):
        jtp.states_from_panel(np.zeros((3, 21), dtype=bool))


# --------------------------------------------------------------------------- #
# ACCEPTANCE #2 : workspace.py tourne inchangé sur les traces J-lens Track P (persona)
# --------------------------------------------------------------------------- #
def test_workspace_pipeline_runs_on_trackP_traces(trackP_npz):
    """End-to-end : traces J-Lens Track P -> adaptateur -> batterie workspace.

    Prouve l'acceptance #2 de #5681 (déclinée Track P) : :mod:`ict.workspace`
    consomme les traces persona via l'adaptateur SANS modification. L'ignition
    temporelle plantee dans le prompt (``persona_cautious``, 0) doit etre detectee
    (preuve qualitative non triviale : le pipeline fonctionne sur persona, pas juste
    qu'il s'execute)."""
    tr = jtp.load_traces(trackP_npz)
    feats = jtp.differential_features(tr, k=12)           # feature 7 ressortira
    assert 7 in set(feats.tolist())                      # precond : l'ignition est dans le panel
    panels = jtp.acts_topk_panels(tr, feats)
    acts = panels[("persona_cautious", 0)]               # (T, 12) : le prompt a ignition plantee

    # concentration par pas -> l'ignition plantee cree un saut
    conc = workspace.concentration_series(acts, metric="gini")
    assert conc.shape == (T,)
    half = T // 2
    assert conc[half:].mean() > conc[:half].mean()       # la 2e moitie est plus concentree

    # Detection d'ignitions (lecture Dehaene temporelle)
    events = workspace.ignition_events(conc, threshold=0.5, persistence=5)
    assert len(events) >= 1                              # l'ignition plantee est detectee
    assert all(e["center"] >= half - 5 for e in events)  # ... dans la 2e moitie

    # discretisation -> batterie event-triggered
    bits = jtp.binarize_quantile(acts, q=0.7)
    states = jtp.states_from_panel(bits)
    rng = np.random.default_rng(0)
    battery = workspace.event_triggered_battery(
        states, [e["center"] for e in events], window=15,
        rng=rng, n_shuffles=10, n_neutral=len(events),
    )
    assert battery["n_events"] == len(events)
    assert "contrast" in battery
    assert -1e-9 <= battery["ec_gain_event"]              # gain real, signe honnete
    assert isinstance(battery["fraction_credited_events"], float)


# --------------------------------------------------------------------------- #
# Integration : schema des traces reelles Track P (si jamais committes)
# --------------------------------------------------------------------------- #
REAL = Path(__file__).parent.parent / "traces"


@pytest.mark.parametrize("variant", ["trained", "control"])
def test_real_trackP_traces_schema(variant):
    path = REAL / f"ict_trackP_jlens_layer16_{variant}.npz"
    if not path.exists():
        pytest.skip("traces J-Lens Track P reelles absentes (extraction GPU2 "
                    "de #5681 Track P non livree)")
    tr = jtp.load_traces(path)
    assert tr["meta"]["lens"] == "jacobian"
    assert tr["meta"]["track"].startswith("P")
    assert tr["meta"]["k"] == K_TOPK and tr["meta"]["d_sae"] > 0
    assert "persona" in str(tr["meta"].get("persona_sets", ""))   # au moins un set persona
    for e in tr["prompts"].values():
        assert e["ids"].shape[1] == K_TOPK
