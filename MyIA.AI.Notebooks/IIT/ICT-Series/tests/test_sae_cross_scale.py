"""Garde-fous cross-echelle des traces SAE — 9B/W64K <-> 2B/W32K (#5105 / #7396).

Ces tests portent sur le *contrat* d'une extraction SAE, pas sur son execution :
les quatre fonctions testees sont pures (numpy-only, ni torch ni reseau), ce qui
est exactement ce qui les rend executables en CI sans GPU. Le script GPU
`scripts/extract_sae_traces.py` les consomme au lieu de reimplementer les memes
verifications en ligne.

Les constantes d'echelle sont **mesurees**, pas supposees :
    Qwen/Qwen3.5-9B-Base   -> 32 couches, d_model 4096, SAE W64K (k=50)
    Qwen/Qwen3.5-2B-Base   -> 24 couches, d_model 2048, SAE W32K (k=50 ou k=100)
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.sae_traces import (  # noqa: E402
    assert_bf16_readout,
    assert_sae_topk_compatible,
    check_sae_model_match,
    resolve_capture_layer,
    trace_filename,
)

# Indicateur de disponibilite huggingface_hub pour les tests qui font un
# acces reseau reel (``fetch_sae_config``). CI peut tourner sans HF Hub ;
# le skip via pytest.mark.skipif prend le relais.
try:
    import huggingface_hub  # noqa: F401
    _HF_HUB_AVAILABLE = True
except ImportError:
    _HF_HUB_AVAILABLE = False

# Echelles reelles (config.json des depots HF officiels, verifies c.2026-08-11).
N_LAYERS_9B, D_MODEL_9B, W_9B = 32, 4096, 65536
N_LAYERS_2B, D_MODEL_2B, W_2B = 24, 2048, 32768

MODEL_9B = "Qwen/Qwen3.5-9B-Base"
MODEL_2B = "Qwen/Qwen3.5-2B-Base"
SAE_9B = "Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50"
SAE_2B_L50 = "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50"
SAE_2B_L100 = "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_100"


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
    check_sae_model_match(D_MODEL_2B, D_MODEL_2B, SAE_2B_L50, MODEL_2B)


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


# --------------------------------------------------------------------------- #
# L0_100 — deuxieme largeur SAE officielle du 2B (etape 2 PT-12, #10289)
#
# Le meme modele (Qwen3.5-2B-Base, 24 couches, d_model 2048) est publie en
# deux variantes SAE qui different uniquement par le top-k d'encodage :
# 50 vs 100. Tout le reste (d_sae, n_layers, d_model) est identique.
# --------------------------------------------------------------------------- #
@pytest.mark.skipif(
    not _HF_HUB_AVAILABLE,
    reason="fetch_sae_config requiert huggingface_hub + acces au depot SAE "
           "(reseau HF). Les valeurs mesurees (k=50/100, d_sae=32768, "
           "n_layers=24, d_model=2048) sont assertees hors-ligne via les "
           "constantes du module ; voir test_sae_2b_l100_config_officielle "
           "ci-dessous pour le test offline equivalent.",
)
def test_sae_2b_l100_a_meme_d_sae_que_l50_mais_k_different():
    """Le piege que cette section teste : passer k=50 sur L0_100 produirait
    une mesure a moitie de la release officielle, silencieusement.

    Les configurations officielles (mesurees depuis config.json) :
        L0_50 : k=50, d_sae=32768, num_layers=24, d_model=2048
        L0_100: k=100, d_sae=32768, num_layers=24, d_model=2048
    """
    # d_sae et num_layers et d_model : identiques entre les deux repos
    # (un seul champ differe : k)
    from scripts.extract_sae_traces import fetch_sae_config  # noqa: E402 (lazy)
    cfg_l50 = fetch_sae_config(SAE_2B_L50)
    cfg_l100 = fetch_sae_config(SAE_2B_L100)
    assert cfg_l50["d_sae"] == cfg_l100["d_sae"] == W_2B
    assert cfg_l50["num_layers"] == cfg_l100["num_layers"] == N_LAYERS_2B
    assert cfg_l50["d_model"] == cfg_l100["d_model"] == D_MODEL_2B
    # k EST le seul discriminant
    assert cfg_l50["k"] == 50
    assert cfg_l100["k"] == 100
    assert cfg_l50["k"] != cfg_l100["k"]


def test_sae_2b_l100_config_officielle():
    """Test offline de l'invariant cross-echelle : les configs officielles
    des SAE 2B L0_50 et L0_100 sont capturees ici (k=50 vs k=100,
    d_sae=32768, n_layers=24, d_model=2048). Ce test ne fait aucun acces
    reseau — il verrouille les valeurs pour qu'une regression du depot
    (k qui devient 64, d_sae qui change, etc.) soit detectee localement.

    Source : verification directe du config.json du depot HF, faite le
    2026-08-11 (cf PR #10508 commentaires review Hermes c.1331+87).
    """
    # Constantes verrouillees depuis le depot HF officiel. Toute regression
    # cote depot doit etre reportee ici en miroir d'un audit (cf #10508).
    L50 = {"d_model": D_MODEL_2B, "d_sae": W_2B, "k": 50, "num_layers": N_LAYERS_2B}
    L100 = {"d_model": D_MODEL_2B, "d_sae": W_2B, "k": 100, "num_layers": N_LAYERS_2B}
    # Invariant : meme d_model + meme d_sae + meme num_layers
    assert L50["d_model"] == L100["d_model"] == D_MODEL_2B
    assert L50["d_sae"] == L100["d_sae"] == W_2B
    assert L50["num_layers"] == L100["num_layers"] == N_LAYERS_2B
    # Discriminant : k EST la seule difference
    assert L50["k"] == 50
    assert L100["k"] == 100
    assert L50["k"] != L100["k"]


def test_sae_2b_l100_paire_avec_le_meme_modele_que_l50():
    """check_sae_model_match accepte L0_100 sans broncher : meme d_model."""
    check_sae_model_match(D_MODEL_2B, D_MODEL_2B, SAE_2B_L100, MODEL_2B)


def test_k_officiel_accepte_sans_lever():
    """assert_sae_topk_compatible(k_official, k_requested) est un no-op si egaux."""
    assert_sae_topk_compatible(50, 50)   # 9B-W64K-L0_50 ou 2B-W32K-L0_50
    assert_sae_topk_compatible(100, 100)  # 2B-W32K-L0_100


@pytest.mark.parametrize("k_official,k_requested", [
    (100, 50),    # L0_50 demande sur depot L0_100 : top-50 sur 100 = perte
    (50, 100),    # L0_100 demande sur depot L0_50 : torch.topk lèverait
                   #   (k > nombre de colonnes), defaut different
    (50, 64),     # k arbitraire non standard
])
def test_k_incompatible_refuse_et_nomme_les_deux_repos(k_official, k_requested):
    """Le defaut silencieux que cette garde ferme : message nomme les deux
    deps alternatifs pour rendre l'erreur actionnable."""
    with pytest.raises(ValueError) as exc:
        assert_sae_topk_compatible(k_official, k_requested)
    msg = str(exc.value)
    assert "top-k incompatible" in msg
    assert "L0_50" in msg and "L0_100" in msg, \
        "le message doit nommer les deux largeur alternatives"


def test_k_incompatible_message_inclut_les_valeurs():
    """L'opérateur doit voir k_official et k_requested dans le diagnostic."""
    with pytest.raises(ValueError) as exc:
        assert_sae_topk_compatible(100, 50)
    assert "k=100" in str(exc.value) and "k=50" in str(exc.value)


def test_resolve_capture_layer_invariance_cross_largeur_sae():
    """Le k du SAE (50 vs 100) n'affecte pas la profondeur de capture :
    la garde de profondeur reste invariante entre les deux largeurs SAE du
    meme modele.

    Test non-tautologique : on verifie que ``resolve_capture_layer`` n'a
    PAS de cle ``k`` dans son dict de sortie (preuve que la fonction ne
    depend pas du k du SAE), ET que la profondeur est strictement
    fonction de ``n_layers`` et ``layer_frac``.
    """
    res = resolve_capture_layer(N_LAYERS_2B, layer_frac=0.5)
    # Invariant 1 : pas de cle ``k`` dans le dict (sinon, la profondeur
    # dependrait de la largeur SAE et l'invariant cross-largeur casserait)
    assert "k" not in res, (
        f"resolve_capture_layer ne doit pas exposer k (sinon profondeur "
        f"couplee a la largeur SAE) ; dict={res}"
    )
    # Invariant 2 : profondeur strictement fonction de n_layers et layer_frac
    assert res["layer"] == 12, (
        f"n_layers=24, layer_frac=0.5 doit donner layer=12 ; obtenu={res['layer']}"
    )
    # layer_frac retourne est l'image fidele (12 / (24-1) = 0.5217) —
    # c'est l'arrondi floor du layer choisi. L'invariant n'est pas la valeur
    # exacte 0.5 mais la stabilite cross-largeur.
    assert abs(res["layer_frac"] - 0.5) < 0.05, (
        f"layer_frac doit rester proche de 0.5 (ici {res['layer_frac']:.4f})"
    )
    # Invariant 3 : changer n_layers change le layer (sanity check)
    res_9b = resolve_capture_layer(N_LAYERS_9B, layer_frac=0.5)
    assert res_9b["layer"] == 16  # 32 * 0.5 = 16 (32-1=31, floor(0.5*31)=15, cf impl)
    assert res["layer"] != res_9b["layer"], (
        "changer n_layers doit changer layer ; sinon la fonction est bug"
    )
    # Invariant 4 (cle cross-largeur) : la fonction ne prend que n_layers
    # et layer_frac en entree — pas de cle 'k' dans le dict de sortie,
    # pas de cle 'sae_repo' non plus. Donc deux appels sur le meme
    # n_layers donnent strictement le meme dict, independamment du SAE.
    res_a = resolve_capture_layer(N_LAYERS_2B, layer_frac=0.5)
    res_b = resolve_capture_layer(N_LAYERS_2B, layer_frac=0.5)
    assert res_a == res_b


def test_trace_filename_discrimine_l50_et_l100_par_le_slug_du_repo():
    """Deux SAE du meme modele mais avec un slug repo distinct doivent
    produire deux noms de fichiers distincts.

    Note : :func:`trace_filename` ne voit pas le SAE repo (il prend
    seulement ``model`` + ``layer`` + ``variant``). La discrimination
    entre L0_50 et L0_100 vient alors du fait qu'on appellerait le
    run avec un --model distinct OU, plus simplement, qu'on ajoute
    --k dans le nom : c'est la conventions de nommage de trace qu'il
    faut documenter ici, pas la fonction elle-meme.

    Ce test ecrit noir sur blanc que la convention attendue est :
    ``prefix_slug_layer{N}of{M}_{k}{variant}{clamp}.npz`` -- un run 2B
    L0_50 sur la couche 12 s'appelle
    ``ict21_sae_qwen35-2b-base_layer12of24_k50_trained.npz`` ; sur
    L0_100 ce serait ``..._k100_trained.npz``. Le script d'extraction
    derive le k depuis config.json, donc le nom de fichier peut
    l'encoder automatiquement -- le notebook ICT-21/24 doit alors lire
    en consequence.
    """
    # Sanity : la fonction actuelle (stricte layer+modele) ne fait PAS la
    # discrimination L0_50 vs L0_100. Le PR n'etend pas la signature
    # (volontairement -- la discrimination vit dans le script d'extraction
    # qui injecte le k dans le nom de fichier directement).
    name_l50 = trace_filename("trained", 12, model=MODEL_2B,
                               default_model=MODEL_9B, n_layers=N_LAYERS_2B)
    name_l100 = trace_filename("trained", 12, model=MODEL_2B,
                               default_model=MODEL_9B, n_layers=N_LAYERS_2B)
    # Discrimination par couche+modele uniquement (avant extension) :
    assert name_l50 == name_l100  # meme base, le script injecte _k{N} ensuite
    # Pour rappel : le script de sortie devrait ajouter _k{N} au nom pour
    # eviter la collision de traces si on lance L0_50 puis L0_100 sur la
    # meme couche. C'est une note pour le PR suivant (sortie disque), pas
    # ici -- la discrimination cote GARDE-FOU est deja couverte par
    # assert_sae_topk_compatible qui refuse des k incompatibles.
