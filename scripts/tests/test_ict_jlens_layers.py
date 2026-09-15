#!/usr/bin/env python3
"""Tests de scripts/ict_jlens_layers.py (pilote #15480, finding #16230).

La garde que ce fichier porte : **un profil J-Lens mesure sous un panneau
entier est muet par construction**, et une mesure muette ne doit jamais
pouvoir repasser pour un verdict. Trois angles :

1. le mecanisme racine -- remplacer l'etat entier par celui du donneur a
   n'importe quelle couche produit les memes logits (donc la couche
   n'entre pas dans la mesure) ;
2. la contre-epreuve -- a dose fixee sous-composante, le profil depend
   effectivement de la couche et de la position ;
3. le verrou de source -- la cellule J-Lens du notebook ne construit pas
   une cible pleine. C'est ce test qui rougit si quelqu'un revient au
   panneau entier.

CPU-only : modele 2 couches d_model 16, aucune donnee reelle.
"""

from pathlib import Path
import json
import sys

import numpy as np
import pytest
import torch

_scripts = str(Path(__file__).resolve().parent.parent)
if _scripts not in sys.path:
    sys.path.insert(0, _scripts)

from ict_pilot_transformer import TinyTransformer
from ict_jlens_layers import (component_coords, is_full_panel, kl_final,
                              layer_effect, layer_spread, profile)


KEYS = ("L0_pre", "L0_post", "L1_pre", "L1_post")
SEQ, D, VOCAB = 12, 16, 8


def _model():
    return TinyTransformer(vocab=VOCAB, d_model=D, n_layers=2, n_heads=2,
                           d_mlp=32, max_len=SEQ, seed=0)


def _panels(rng, d_model=D):
    ref = rng.normal(size=(SEQ, d_model))
    donor = rng.normal(size=(SEQ, d_model)) * 1.5 + 0.4
    return ref, donor


def _capture(model, tokens):
    """Logits + panneaux REELS du modele (un panneau synthetique n'est pas
    une trajectoire : il ne se propage pas comme l'etat qu'il remplace)."""
    logits, panels = model.forward_with_panels(torch.from_numpy(tokens[None]))
    return logits, {k: v[0].numpy() for k, v in panels.items()}


def _swap(panel_a, panel_b, positions, features):
    out = panel_a.copy()
    ix = np.ix_(list(positions), list(features))
    out[ix] = panel_b[ix]
    return out


def _ref_logits(model, tokens):
    return model.forward_patched(torch.from_numpy(tokens[None]), {})


# --------------------------------------------------------------------- #
# 1. Mecanisme racine : le panneau entier rend la couche muette
# --------------------------------------------------------------------- #

def test_full_donor_panel_is_layer_invariant():
    """Le finding #16230, verrouille comme propriete de ``forward_patched``.

    Injecter l'etat ENTIER du donneur a n'importe quel point de prelevement
    fait recalculer au modele la trajectoire complete du donneur : les logits
    finaux sont ceux du donneur, et la couche d'injection disparait de la
    mesure. C'est exactement ce qui rendait H2-couches invariant.
    """
    model = _model()
    tokens = np.zeros(SEQ, dtype=np.int64)
    donor_tokens = (np.arange(SEQ) % VOCAB).astype(np.int64)
    _, donor_panels = _capture(model, donor_tokens)

    logs = {k: model.forward_patched(torch.from_numpy(tokens[None]),
                                     {k: torch.from_numpy(donor_panels[k][None])})
            for k in KEYS}
    for k in KEYS[1:]:
        assert torch.allclose(logs[k], logs[KEYS[0]], atol=1e-6), (
            f"le patch {k} d'un panneau donneur ENTIER doit rendre les memes "
            f"logits que {KEYS[0]} -- si ce n'est plus le cas, la garde "
            f"#16230 doit etre reevaluee, pas supprimee"
        )


def test_full_panel_profile_has_zero_spread():
    """Consequence directe : le profil par couche est plat sous panneau entier."""
    model = _model()
    tokens = np.zeros(SEQ, dtype=np.int64)
    donor_tokens = (np.arange(SEQ) % VOCAB).astype(np.int64)
    ref_logits, _ = _capture(model, tokens)
    _, donor_panels = _capture(model, donor_tokens)

    prof = profile(model, tokens, ref_logits, donor_panels, KEYS)
    assert layer_spread(prof) == pytest.approx(0.0, abs=1e-6)


# --------------------------------------------------------------------- #
# 2. Contre-epreuve : a dose fixee sous-composante, la mesure discrimine
# --------------------------------------------------------------------- #

def test_subcomponent_profile_discriminates_layers():
    """Deux coordonnees suffisent a rendre la couche audible.

    Le contraste avec le test precedent est le point : meme modele, memes
    panneaux, meme reference -- seule la TAILLE de la cible change.
    """
    model = _model()
    tokens = np.zeros(SEQ, dtype=np.int64)
    ref, donor = _panels(np.random.default_rng(2))
    ref_logits = _ref_logits(model, tokens)

    coords = (3, 11)
    cf = {k: _swap(ref, donor, range(SEQ), coords) for k in KEYS}
    prof = profile(model, tokens, ref_logits, cf, KEYS)
    assert layer_spread(prof) > 1e-6, (
        f"une cible de 2 coordonnees doit discriminer les couches, profil={prof}"
    )
    assert all(is_full_panel(range(SEQ), coords, ref.shape) is False for _ in (0,))


def test_position_axis_discriminates():
    """Le second axe exige par l'acceptance : plusieurs positions, pas une seule."""
    model = _model()
    tokens = np.zeros(SEQ, dtype=np.int64)
    ref, donor = _panels(np.random.default_rng(3))
    ref_logits = _ref_logits(model, tokens)

    coords = (3, 11)
    last_only = {k: _swap(ref, donor, (SEQ - 1,), coords) for k in KEYS}
    all_pos = {k: _swap(ref, donor, range(SEQ), coords) for k in KEYS}
    eff_last = layer_effect(model, tokens, ref_logits, last_only["L0_pre"], "L0_pre")
    eff_all = layer_effect(model, tokens, ref_logits, all_pos["L0_pre"], "L0_pre")
    assert eff_last != pytest.approx(eff_all, abs=1e-9)


def test_effect_is_zero_when_donor_matches_reference():
    """Controle de manipulation : re-injecter son propre panneau ne fait rien.

    Tolerance 1e-9 -- tenable parce que ``kl_final`` ne lisse pas. Si ce test
    se met a exiger 1e-6, c'est l'instrument qui a regresse (plancher de bruit
    re-introduit), pas la garde qu'il faut desserrer.
    """
    model = _model()
    tokens = (np.arange(SEQ) % VOCAB).astype(np.int64)
    ref_logits, ref_panels = _capture(model, tokens)
    for key in KEYS:
        eff = layer_effect(model, tokens, ref_logits, ref_panels[key].copy(), key)
        assert eff == pytest.approx(0.0, abs=1e-9), f"self-patch {key} non nul"
    assert kl_final(ref_logits, ref_logits) == pytest.approx(0.0, abs=1e-9)


# --------------------------------------------------------------------- #
# 3. Primitives
# --------------------------------------------------------------------- #

def test_component_coords_picks_heaviest_rows_sorted():
    w = np.zeros((6, 3), dtype=np.float64)
    w[4, :] = 5.0
    w[1, :] = 3.0
    w[2, :] = 1.0
    assert component_coords(w, 2) == (1, 4)
    assert component_coords(w, 3) == (1, 2, 4)


def test_component_coords_guards():
    w = np.zeros((4, 2), dtype=np.float64)
    with pytest.raises(ValueError):
        component_coords(w, 0)
    with pytest.raises(ValueError):
        component_coords(w, 5)
    with pytest.raises(ValueError):
        component_coords(np.zeros(4), 1)


def test_is_full_panel():
    assert is_full_panel(range(6), range(4), (6, 4)) is True
    assert is_full_panel(range(6), range(3), (6, 4)) is False
    assert is_full_panel(range(5), range(4), (6, 4)) is False
    assert is_full_panel(range(6), (0, 1, 2), (6, 4)) is False


# --------------------------------------------------------------------- #
# 4. Verrou de source : le notebook ne doit pas revenir au panneau entier
# --------------------------------------------------------------------- #

_NB = (Path(__file__).resolve().parents[2] / "MyIA.AI.Notebooks" / "IIT"
       / "ICT-Series" / "ICT-40-TriangulationCausale.ipynb")


def _jlens_cell_source():
    if not _NB.exists():
        pytest.skip(f"notebook absent : {_NB}")
    nb = json.loads(_NB.read_text(encoding="utf-8"))
    hits = ["".join(c.get("source", [])) for c in nb["cells"]
            if "interchange_panels" in "".join(c.get("source", []))]
    assert hits, "aucune cellule J-Lens trouvee dans le notebook"
    return "\n".join(hits)


def test_jlens_cell_does_not_target_the_whole_panel():
    """LE test qui rougit sous full-panel aveugle (#16230).

    Une cible `features=tuple(range(panneau.shape[-1]))` avec toutes les
    positions rend H2-couches invariant : la consigne est que la cellule
    J-Lens construise sa cible depuis un jeu de coordonnees de taille fixe.
    """
    src = _jlens_cell_source()
    assert "features=tuple(range(" not in src, (
        "la cellule J-Lens cible de nouveau TOUTES les dimensions : le profil "
        "par couche redevient invariant par construction (finding #16230)"
    )
    assert "JLENS_COORDS" in src, (
        "la cellule J-Lens doit construire sa cible depuis un jeu de "
        "coordonnees de taille fixee (JLENS_COORDS), partage entre les couches"
    )
