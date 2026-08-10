"""Garde-fous cross-echelle des traces SAE — 9B/W64K <-> 2B/W32K (#5105 / #7396).

Ces tests portent sur le *contrat* d'une extraction SAE, pas sur son execution :
les quatre fonctions testees sont pures (numpy-only, ni torch ni reseau), ce qui
est exactement ce qui les rend executables en CI sans GPU. Le script GPU
`scripts/extract_sae_traces.py` les consomme au lieu de reimplementer les memes
verifications en ligne.

Les constantes d'echelle sont **mesurees**, pas supposees :
    Qwen/Qwen3.5-9B-Base   -> 32 couches, d_model 4096, SAE W64K
    Qwen/Qwen3.5-2B-Base   -> 24 couches, d_model 2048, SAE W32K
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.sae_traces import (  # noqa: E402
    assert_bf16_readout,
    check_sae_model_match,
    resolve_capture_layer,
    trace_filename,
)

# Echelles reelles (config.json des depots HF officiels).
N_LAYERS_9B, D_MODEL_9B, W_9B = 32, 4096, 65536
N_LAYERS_2B, D_MODEL_2B, W_2B = 24, 2048, 32768

MODEL_9B = "Qwen/Qwen3.5-9B-Base"
MODEL_2B = "Qwen/Qwen3.5-2B-Base"
SAE_9B = "Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50"
SAE_2B = "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50"


# --------------------------------------------------------------------------- #
# resolve_capture_layer
# --------------------------------------------------------------------------- #
def test_layer_absolu_conserve_et_annote():
    """Un index absolu passe tel quel, mais ressort avec sa profondeur relative."""
    got = resolve_capture_layer(N_LAYERS_9B, layer=16)
    assert got["layer"] == 16
    assert got["n_layers"] == 32
    assert got["layer_frac"] == pytest.approx(16 / 31, abs=1e-4)


def test_le_meme_index_designe_deux_profondeurs_differentes():
    """Le piege que ces gardes existent pour rendre visible.

    `--layer 16` est accepte sur les deux echelles et n'y a pas le meme sens :
    mi-reseau sur le 9B, ~70 % de la profondeur sur le 2B. Sans la profondeur
    relative dans les metadonnees, un differentiel entre ces deux traces
    melangerait l'effet cherche et un artefact de profondeur — sans erreur.
    """
    frac_9b = resolve_capture_layer(N_LAYERS_9B, layer=16)["layer_frac"]
    frac_2b = resolve_capture_layer(N_LAYERS_2B, layer=16)["layer_frac"]
    assert frac_9b == pytest.approx(0.5161, abs=1e-3)
    assert frac_2b == pytest.approx(0.6957, abs=1e-3)
    assert abs(frac_2b - frac_9b) > 0.17, "l'ecart de profondeur doit rester visible"


def test_layer_frac_transpose_l_intention_entre_echelles():
    """0.5 = mi-reseau, quelle que soit la profondeur : 16 sur 32, 12 sur 24."""
    assert resolve_capture_layer(N_LAYERS_9B, layer_frac=0.5)["layer"] == 16
    assert resolve_capture_layer(N_LAYERS_2B, layer_frac=0.5)["layer"] == 12


@pytest.mark.parametrize("frac,expected_9b", [(0.0, 0), (0.25, 8), (1.0, 31)])
def test_layer_frac_bornes(frac, expected_9b):
    assert resolve_capture_layer(N_LAYERS_9B, layer_frac=frac)["layer"] == expected_9b


def test_exactement_un_parametre_requis():
    with pytest.raises(ValueError, match="exactement un"):
        resolve_capture_layer(N_LAYERS_9B)
    with pytest.raises(ValueError, match="exactement un"):
        resolve_capture_layer(N_LAYERS_9B, layer=16, layer_frac=0.5)


def test_couche_hors_bornes_refusee_avec_la_profondeur_reelle():
    """Le defaut 16 est valide sur 32 couches ; 28 ne l'est pas sur 24."""
    with pytest.raises(ValueError, match=r"24 couches"):
        resolve_capture_layer(N_LAYERS_2B, layer=28)
    with pytest.raises(ValueError, match="hors bornes"):
        resolve_capture_layer(N_LAYERS_2B, layer=N_LAYERS_2B)   # index == n_layers
    with pytest.raises(ValueError, match="hors bornes"):
        resolve_capture_layer(N_LAYERS_9B, layer=-1)


def test_layer_frac_hors_intervalle_refuse():
    with pytest.raises(ValueError, match=r"hors \[0, 1\]"):
        resolve_capture_layer(N_LAYERS_9B, layer_frac=1.5)


def test_n_layers_absent_de_la_config_refuse():
    """`getattr(cfg, "num_hidden_layers", None)` peut rendre None : le dire."""
    with pytest.raises(ValueError, match="num_hidden_layers"):
        resolve_capture_layer(None, layer=16)


# --------------------------------------------------------------------------- #
# check_sae_model_match
# --------------------------------------------------------------------------- #
def test_appariements_corrects_passent():
    check_sae_model_match(D_MODEL_9B, D_MODEL_9B, SAE_9B, MODEL_9B)
    check_sae_model_match(D_MODEL_2B, D_MODEL_2B, SAE_2B, MODEL_2B)


def test_sae_9b_sur_modele_2b_refuse_et_nomme_l_appariement():
    """La confusion realiste : changer --model sans changer --sae-repo."""
    with pytest.raises(ValueError) as exc:
        check_sae_model_match(D_MODEL_9B, D_MODEL_2B, SAE_9B, MODEL_2B)
    msg = str(exc.value)
    assert "4096" in msg and "2048" in msg
    assert "W32K" in msg, "le message doit nommer le SAE a utiliser a la place"


def test_message_utilisable_sans_les_noms_de_depots():
    """Appel bibliotheque sans repo/model : le message reste lisible."""
    with pytest.raises(ValueError, match="d_model incompatible"):
        check_sae_model_match(D_MODEL_2B, D_MODEL_9B)


# --------------------------------------------------------------------------- #
# assert_bf16_readout
# --------------------------------------------------------------------------- #
def test_readout_bf16_accepte():
    assert_bf16_readout(None)


def test_readout_sur_checkpoint_quantifie_refuse():
    with pytest.raises(ValueError, match="bf16"):
        assert_bf16_readout({"quant_method": "bitsandbytes", "bits": 4})


def test_readout_quantifie_autorise_explicitement():
    """Exploration assumee : possible, mais elle doit etre demandee."""
    assert_bf16_readout({"quant_method": "awq"}, allow_quantized=True)


def test_le_message_explique_le_regime_correct():
    """QLoRA pour l'entrainement, bf16 fusionne pour la lecture."""
    with pytest.raises(ValueError) as exc:
        assert_bf16_readout({"bits": 4})
    assert "NF4" in str(exc.value)


# --------------------------------------------------------------------------- #
# trace_filename — le defaut le plus couteux : la collision silencieuse
# --------------------------------------------------------------------------- #
def test_nom_historique_conserve_a_l_octet():
    """Les traces committees et les notebooks ICT-21/24 les chargent par chemin."""
    assert trace_filename("trained", 16, model=MODEL_9B, default_model=MODEL_9B,
                          n_layers=N_LAYERS_9B) == "ict21_sae_layer16_trained.npz"
    assert trace_filename("control", 16, model=MODEL_9B, default_model=MODEL_9B,
                          n_layers=N_LAYERS_9B) == "ict21_sae_layer16_control.npz"


def test_clamp_suffixe_conserve():
    assert trace_filename("trained", 16, model=MODEL_9B, default_model=MODEL_9B,
                          n_layers=N_LAYERS_9B, n_clamp=3) == \
        "ict21_sae_layer16_trained_clamp3.npz"


def test_deux_echelles_a_la_meme_couche_ne_collisionnent_pas():
    """Le defaut le plus couteux du lot : un run ecrasant l'autre en silence.

    Sans slug d'echelle, un run 2B et un run 9B a la couche 16 ecrivent le meme
    nom de fichier — perte de donnees, pas seulement confusion.
    """
    name_9b = trace_filename("trained", 16, model=MODEL_9B,
                             default_model=MODEL_9B, n_layers=N_LAYERS_9B)
    name_2b = trace_filename("trained", 16, model=MODEL_2B,
                             default_model=MODEL_9B, n_layers=N_LAYERS_2B)
    assert name_9b != name_2b
    assert "qwen35-2b-base" in name_2b
    assert "layer16of24" in name_2b, "la profondeur totale doit rester lisible"


def test_slug_insere_des_que_le_modele_differe_meme_sans_n_layers():
    name = trace_filename("trained", 12, model=MODEL_2B, default_model=MODEL_9B)
    assert name.startswith("ict21_sae_qwen35-2b-base_layer12_")


def test_sans_modele_le_nom_reste_le_defaut_historique():
    """Appel sans --model explicite : pas de slug parasite."""
    assert trace_filename("trained", 16) == "ict21_sae_layer16_trained.npz"
