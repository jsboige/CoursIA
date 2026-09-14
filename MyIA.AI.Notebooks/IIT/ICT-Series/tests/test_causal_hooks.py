"""Tests des hooks torch du moteur causal (Epic #15475, grain #15479 tranche 2).

Couvre ``scripts/causal_hooks.py`` — le confinement torch du moteur — sur des
modeles jouets CPU deterministes (LayerNorm + Linear, seeds fixes, float64
pour la parite bit a bit avec le coeur numpy). Aucune capture GPU : torch est
importe paresseusement via ``pytest.importorskip`` DANS chaque test (convention
``test_jlens_traces.py``) pour que la collecte reste verte sur un env sans
torch (CI ICT py3.9 sans torch : les tests comptent au floor-guard et sautent
a l'execution, jamais a la collecte).

Gates :
  1. (Miroir numpy) ``apply_spec_to_tensor`` == ``apply_intervention`` bit a
     bit pour les 4 operations unaires ; interchange == cote de
     ``interchange_panels``.
  2. (Non-mutation + remplacement) le tensor d'entree n'est JAMAIS mute ; le
     forward hooked == edition manuelle puis forward propre (bit a bit).
  3. (Validation forte) position/feature hors panneau, donneur de mauvaise
     forme, module inconnu, absence de tensor : chaque echec NOMME sa cause.
  4. (Controles through-hooks) sham de clamp = write-back = identite ; bras
     intact Gate 24 = identite PAR LA MEME VOIE ; cible aleatoire appariee
     passe par le meme chemin d'application.
  5. (Captures) panneaux/tranche avant-apres, point de lecture readout post.
  6. (Protocole interchange) capture-puis-ecriture echange exactement les
     tranches ; ecrire avant de capturer echoue avec diagnostic.
  7. (Sidecar) ``hook_record`` produit un enregistrement complet (verdict,
     empreintes distinctes, JSON serialisable).
"""
from __future__ import annotations

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict.causal_engine import (  # noqa: E402
    InterventionSpec,
    apply_intervention,
    build_gate24_family,
    interchange_panels,
    random_target_matched,
    sham_of,
)

D = 8
T = 6


def _torch():
    return pytest.importorskip("torch")


def _spec(operation: str, **overrides) -> InterventionSpec:
    """Spec de reference sur le panneau jouet (T=6, d=8), champs par defaut sains."""
    base = dict(
        operation=operation,
        instrument="synthetic",
        layer=0,
        positions=(1, 2),
        features=(4, 5),
        dose=2.0,
        direction=(1.0, 0.0) if operation in ("clamp", "steer") else None,
        donor=((1.5, -2.5), (-3.5, 4.5)) if operation == "patch" else None,
        run="hook-run",
        seed=11,
    )
    if operation == "interchange":
        base["paired_run"] = "hook-run-paired"
    base.update(overrides)
    return InterventionSpec(**base)


def _panel(seed: int = 7) -> np.ndarray:
    return np.random.default_rng(seed).normal(size=(T, D))


def _model():
    """Modele jouet deterministe : LayerNorm(d) puis Linear(d, d), float64."""
    torch = _torch()
    torch.manual_seed(0)
    model = torch.nn.Sequential(
        torch.nn.LayerNorm(D, dtype=torch.float64),
        torch.nn.Linear(D, D, dtype=torch.float64),
    )
    model.eval()
    return model


def _x(panel: np.ndarray):
    torch = _torch()
    return torch.tensor(panel, dtype=torch.float64)


# --------------------------------------------------------------------------- #
# Gate 1 : miroir numpy bit a bit
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("operation", ["ablate", "clamp", "steer", "patch"])
def test_tensor_mirror_bitwise_equals_numpy_core(operation):
    """apply_spec_to_tensor reproduit apply_intervention exactement (float64)."""
    _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    panel = _panel()
    spec = _spec(operation)
    got = apply_spec_to_tensor(_x(panel), spec).numpy()
    want = apply_intervention(panel, spec)
    assert got.dtype == want.dtype
    assert np.array_equal(got, want)


def test_interchange_tensor_equals_one_side_of_interchange_panels():
    """L'ecriture d'un cote d'interchange == le cote correspondant du coeur numpy."""
    _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    a, b = _panel(1), _panel(2)
    spec = _spec("interchange")
    donor = b[np.ix_(list(spec.positions), list(spec.features))]
    got = apply_spec_to_tensor(_x(a), spec, donor=donor).numpy()
    want_a, _ = interchange_panels(a, b, spec)
    assert np.array_equal(got, want_a)


def test_empty_target_identity_same_code_path():
    """Cible vide (bras intact) : clone non edite PAR LA MEME VOIE."""
    torch = _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    panel = _panel()
    spec = _spec("clamp", positions=(), features=(), direction=None)
    got = apply_spec_to_tensor(_x(panel), spec)
    assert torch.equal(got, _x(panel))
    assert got is not _x(panel)  # copie, pas un alias


def test_batched_activation_broadcasts_over_batch():
    """(B, T, d) : l'edition s'applique a chaque element du lot, hors cible intact."""
    torch = _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    batch = np.stack([_panel(1), _panel(2)])
    spec = _spec("clamp")
    got = apply_spec_to_tensor(torch.tensor(batch), spec).numpy()
    for b in range(2):
        want = apply_intervention(batch[b], spec)
        assert np.array_equal(got[b], want)


# --------------------------------------------------------------------------- #
# Gate 2 : non-mutation, remplacement d'entrees, equivalence forward
# --------------------------------------------------------------------------- #

def test_input_tensor_never_mutated_by_hook():
    torch = _torch()
    from scripts.causal_hooks import attach_intervention

    model = _model()
    x = _x(_panel())
    snapshot = x.clone()
    spec = _spec("clamp")
    handle = attach_intervention(model, "0", spec)
    try:
        with torch.no_grad():
            model(x)
    finally:
        handle.remove()
    assert torch.equal(x, snapshot)


def test_hooked_forward_equals_manual_edit_then_clean_forward():
    """Le pre-hook REMPLACE l'entree : hooked(x) == model(edite(x)) bit a bit."""
    torch = _torch()
    from scripts.causal_hooks import apply_spec_to_tensor, forward_with_spec

    model = _model()
    x = _x(_panel())
    spec = _spec("clamp")
    hooked, _ = forward_with_spec(model, "0", x, spec, capture_post=False)
    manual = model(apply_spec_to_tensor(x, spec))
    assert torch.equal(hooked, manual)


# --------------------------------------------------------------------------- #
# Gate 3 : validation forte, diagnostics nommes
# --------------------------------------------------------------------------- #

def test_position_and_feature_out_of_range_fail_loudly():
    _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    x = _x(_panel())
    with pytest.raises(ValueError, match="position .* hors activation T=6"):
        apply_spec_to_tensor(x, _spec("clamp", positions=(99,)))
    with pytest.raises(ValueError, match="feature .* hors dimension d=8"):
        apply_spec_to_tensor(x, _spec("clamp", features=(99,), direction=(1.0,)))


def test_donor_wrong_shape_fails_with_both_shapes():
    _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    x = _x(_panel())
    bad = np.zeros((3, 2))  # cible (2, 2)
    with pytest.raises(ValueError, match=r"donneur de forme \(3, 2\) != cible \(2, 2\)"):
        apply_spec_to_tensor(x, _spec("patch", donor=bad))


def test_interchange_without_donor_refuses_direct_write():
    _torch()
    from scripts.causal_hooks import apply_spec_to_tensor

    with pytest.raises(ValueError, match="protocole PairedInterchange"):
        apply_spec_to_tensor(_x(_panel()), _spec("interchange"))


def test_hook_without_tensor_argument_fails_loudly():
    torch = _torch()
    from scripts.causal_hooks import InterventionHook

    hook = InterventionHook(_spec("clamp"))
    with pytest.raises(RuntimeError, match="aucun tensor"):
        hook(torch.nn.LayerNorm(D), ())


def test_attach_unknown_module_names_available_candidates():
    _torch()
    from scripts.causal_hooks import attach_intervention

    with pytest.raises(ValueError, match="disponibles"):
        attach_intervention(_model(), "couche-inexistante", _spec("clamp"))


# --------------------------------------------------------------------------- #
# Gate 4 : controles through-hooks
# --------------------------------------------------------------------------- #

def test_clamp_sham_write_back_is_identity_through_hook():
    """Sham de clamp = write-back de la tranche originale : sortie identique."""
    torch = _torch()
    from scripts.causal_hooks import forward_with_spec

    model = _model()
    panel = _panel()
    x = _x(panel)
    sham = sham_of(_spec("clamp"), panel)
    assert sham.operation == "patch"
    sham_out, handle = forward_with_spec(model, "0", x, sham)
    clean = model(x)
    assert torch.equal(sham_out, clean)
    assert sham.control_ref == "sham-of-clamp(write-back)"


def test_gate24_intact_arm_identity_same_path_target_differs():
    """Bras intact : identite PAR LA MEME VOIE ; bras cible : sortie modifiee."""
    torch = _torch()
    from scripts.causal_hooks import forward_with_spec

    model = _model()
    x = _x(_panel())
    spec = _spec("clamp")
    norms = np.abs(np.random.default_rng(1).normal(1.0, 0.01, size=D))
    control = random_target_matched(
        _panel(), spec, feature_norms=norms,
        feature_freqs=np.full(D, 0.5), rel_tol=1.5,
    )
    family = build_gate24_family(spec, control)
    intact_out, _ = forward_with_spec(model, "0", x, family["intact"], capture_post=False)
    assert torch.equal(intact_out, model(x))
    target_out, _ = forward_with_spec(model, "0", x, family["target"], capture_post=False)
    assert not torch.equal(target_out, model(x))


def test_random_matched_control_applies_through_same_hook_path():
    """Le controle aleatoire apparie traverse le meme chemin d'application."""
    torch = _torch()
    from scripts.causal_hooks import forward_with_spec

    model = _model()
    x = _x(_panel())
    spec = _spec("clamp")
    norms = np.abs(np.random.default_rng(2).normal(1.0, 0.05, size=D))
    control = random_target_matched(
        _panel(), spec, feature_norms=norms,
        feature_freqs=np.full(D, 0.5), rel_tol=0.5,
    )
    clean = model(x)
    target_out, _ = forward_with_spec(model, "0", x, spec, capture_post=False)
    control_out, _ = forward_with_spec(model, "0", x, control, capture_post=False)
    # le controle est une VRAIE intervention (meme nombre de features, autres
    # indices) : il change la sortie, autrement que la cible
    assert not torch.equal(control_out, clean)
    assert not torch.equal(control_out, target_out)


# --------------------------------------------------------------------------- #
# Gate 5 : captures pre/post
# --------------------------------------------------------------------------- #

def test_state_capture_before_after_slices():
    """state_before = tranche du panneau d'entree ; state_after = tranche editee."""
    _torch()
    from scripts.causal_hooks import forward_with_spec

    model = _model()
    panel = _panel()
    x = _x(panel)
    spec = _spec("clamp", dose=3.0, direction=(0.0, 1.0))
    _, handle = forward_with_spec(model, "0", x, spec)
    rows, cols = list(spec.positions), list(spec.features)
    assert np.array_equal(handle.state_before, panel[rows][:, cols])
    want_after = np.tile(np.array([0.0, 3.0]), (len(rows), 1))
    assert np.array_equal(handle.state_after, want_after)
    assert np.array_equal(handle.panel_before, panel)


def test_post_capture_readout_point():
    """capture_post=True : le post-hook capte la sortie du module vise."""
    torch = _torch()
    from scripts.causal_hooks import forward_with_spec

    model = _model()
    x = _x(_panel())
    spec = _spec("clamp", positions=(), features=(), direction=None)  # intact
    with torch.no_grad():
        expected = model[0](x).numpy()
    _, handle = forward_with_spec(model, "0", x, spec)
    assert np.array_equal(handle.readout, expected)
    # et l'edition a bien traverse : state_after vide = rien n'a change
    assert handle.state_after.shape == (0, 0)


# --------------------------------------------------------------------------- #
# Gate 6 : protocole interchange capture-puis-ecriture
# --------------------------------------------------------------------------- #

def test_paired_interchange_swaps_exactly():
    """4 forwards (capture x2, ecriture x2) == interchange_panels du coeur."""
    torch = _torch()
    from scripts.causal_hooks import PairedInterchange

    model = _model()
    a, b = _panel(1), _panel(2)
    spec = _spec("interchange")
    pair = PairedInterchange(spec)

    with torch.no_grad():
        # un hook de capture A LA FOIS : laisse "a" enregistre pendant le
        # forward de b, il re-capturerait b dans le buffer de a
        ha = model[0].register_forward_pre_hook(pair.capture("a"))
        model(_x(a))
        ha.remove()
        hb = model[0].register_forward_pre_hook(pair.capture("b"))
        model(_x(b))
        hb.remove()
    assert np.array_equal(pair.panels["a"], a)
    assert np.array_equal(pair.panels["b"], b)

    h_a = model[0].register_forward_pre_hook(pair.write("a"))
    with torch.no_grad():
        out_a = model(_x(a))
    h_a.remove()
    h_b = model[0].register_forward_pre_hook(pair.write("b"))
    with torch.no_grad():
        out_b = model(_x(b))
    h_b.remove()

    # chaque cote correspond EXACTEMENT au coeur numpy interchange_panels
    want_a, want_b = interchange_panels(a, b, spec)
    assert torch.equal(out_a, model(_x(want_a)))
    assert torch.equal(out_b, model(_x(want_b)))


def test_write_before_both_captures_fails_with_diagnostic():
    _torch()
    from scripts.causal_hooks import PairedInterchange

    pair = PairedInterchange(_spec("interchange"))
    with pytest.raises(ValueError, match="capture les DEUX runs"):
        pair.write("a")


def test_paired_interchange_rejects_non_interchange_spec():
    _torch()
    from scripts.causal_hooks import PairedInterchange

    with pytest.raises(ValueError, match="pas de 'clamp'"):
        PairedInterchange(_spec("clamp"))


# --------------------------------------------------------------------------- #
# Gate 7 : enregistrement sidecar depuis les captures
# --------------------------------------------------------------------------- #

def test_hook_record_full_sidecar():
    """hook_record : verdict selectivite, empreintes distinctes, JSON serialisable."""
    _torch()
    from scripts.causal_hooks import forward_with_spec, hook_record

    model = _model()
    x = _x(_panel())
    spec = _spec("clamp")
    _, handle = forward_with_spec(model, "0", x, spec, capture_post=False)
    rec = hook_record(handle, model="toy-model")
    assert rec.verdict == "selective"
    assert rec.damage["off_target_rel"] == 0.0  # hors cible intact bit a bit
    assert rec.sha_before != rec.sha_after
    payload = rec.to_json()
    assert '"clamp"' in payload
    assert '"toy-model"' in payload
    assert rec.alignment["instrument"] == "synthetic"


def test_hook_record_without_capture_fails():
    _torch()
    from scripts.causal_hooks import InterventionHook, hook_record

    with pytest.raises(ValueError, match="aucune capture"):
        hook_record(InterventionHook(_spec("clamp")))


def test_hook_record_rejects_batched_panel():
    """Panneau (B, T, d) : l'enregistrement sidecar exige le lot unitaire."""
    torch = _torch()
    from scripts.causal_hooks import attach_intervention, hook_record

    model = _model()
    batch = np.stack([_panel(1), _panel(2)])
    x = torch.tensor(batch)
    spec = _spec("clamp")
    handle = attach_intervention(model, "0", spec)
    try:
        with torch.no_grad():
            model(x)
    finally:
        handle.remove()
    with pytest.raises(ValueError, match="lot unitaire"):
        hook_record(handle)
