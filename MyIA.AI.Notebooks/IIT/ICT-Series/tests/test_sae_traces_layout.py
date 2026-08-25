"""Regression #12940 : layout heterogene de W_dec dans ``extract_sae_traces``.

Sonde firsthand de l'issue (checkpoints W32K locaux) :

* ``SAE-Res-Qwen3-1.7B-Base-W32K-L0_50/layer14.sae.pt`` : W_dec (2048, 32768)
* ``SAE-Res-Qwen3-2B-Base-W32K-L0_50/layer12.sae.pt`` : W_dec (2048, 32768)

Le hook de clamp indexait ``W_dec[clamp_ids]`` ou clamp_ids sont des indices
de FEATURES (jusqu'a d_sae-1 = 32767) : sur ces layouts, l'indexation prenait
des lignes = dimensions du residual stream (0..2047). Un clamp_id > 2047 ->
IndexError ; tous < 2048 -> silencieusement faux (directions residuelles
soustraites au lieu des directions decodees des features visees).

``normalize_w_dec`` (meme correctif que ``extract_sae_fidelity.py``, PR
#12938) ramene W_dec en [d_sae, d_model] : l'indexation par feature designe
les directions decodees quel que soit le layout de la release. torch est
autorise dans CE fichier de tests (precedent : test_lens_agreement.py) ; la
bibliotheque ``ict/`` reste numpy-only.
"""

import os
import sys

import torch

_HERE = os.path.dirname(os.path.abspath(__file__))
_SERIES = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_SERIES, "scripts"))

import extract_sae_traces as est  # noqa: E402


def _sae_pair(d_model=64, d_sae=1024):
    """W_enc [d_sae, d_model] + W_dec stocke en [d_model, d_sae] (layout W32K).

    Dimensions compactes preservant l'invariant semantique du fondateur
    (d_model < clamp_id < d_sae, ex. reel : 2048 < 5000 < 32768). Valeurs
    identifiants : arange — chaque ligne i du stockage (dimension residual)
    et chaque colonne j (feature) portent leur index, de sorte qu'une
    mauvaise lecture transposition-dependante est detectable par le contenu,
    pas seulement par la forme."""
    w_enc = torch.arange(d_sae * d_model, dtype=torch.float32).reshape(d_sae, d_model)
    w_dec_stored = torch.arange(d_model * d_sae, dtype=torch.float32).reshape(d_model, d_sae)
    return w_enc, w_dec_stored


def test_w32k_layout_is_transposed_to_sae_rows():
    """Le layout fondateur [d_model, d_sae] (W32K : 2048x32768 reels, 64x1024
    ici) : normalise vers [d_sae, d_model], contenu = transpose exacte."""
    w_enc, w_dec_stored = _sae_pair()
    out = est.normalize_w_dec(w_dec_stored, w_enc)
    assert tuple(out.shape) == (1024, 64)  # [d_sae, d_model]
    assert torch.equal(out, w_dec_stored.t())


def test_canonical_layout_passes_through_unchanged():
    """Une release stockant deja [d_sae, d_model] : inchangee (pas de double
    transposition)."""
    d_model, d_sae = 64, 1024
    w_enc = torch.zeros(d_sae, d_model)
    w_dec = torch.arange(d_sae * d_model, dtype=torch.float32).reshape(d_sae, d_model)
    out = est.normalize_w_dec(w_dec, w_enc)
    assert tuple(out.shape) == (d_sae, d_model)
    assert torch.equal(out, w_dec)


def test_clamp_indexing_selects_feature_directions_not_resid_rows():
    """LA semantique du bug : apres normalisation, W_dec[feature_id] rend la
    direction decodee de la FEATURE (ligne du layout canonique), pas la
    ligne d_model du stockage W32K. Cas mesure de l'issue (reel : clamp_id
    5000 valide feature, > d_model 2048) — IndexError avant, direction
    correcte apres."""
    w_enc, w_dec_stored = _sae_pair()
    w_dec = est.normalize_w_dec(w_dec_stored, w_enc)
    clamp_id = 500  # > d_model (64) et < d_sae (1024) : levait IndexError avant
    row = w_dec[clamp_id]                       # [d_model]
    assert torch.equal(row, w_dec_stored[:, clamp_id])
    # Le clamp a 2 features rend [C, d_model] (l'arite du hook ResidCapture).
    sel = w_dec[[3, clamp_id]]
    assert tuple(sel.shape) == (2, 64)
    assert torch.equal(sel[0], w_dec_stored[:, 3])


def test_resid_row_misread_is_detectably_different():
    """Controle du faux silencieux (tous clamp_ids < d_model) : sans
    normalisation, W_dec_stored[3] rend la ligne 3 du residual stream — une
    direction DIFFERENTE de la direction decodee de la feature 3. Ce test
    documente pourquoi le bug etait invisible a la forme seule."""
    _, w_dec_stored = _sae_pair()
    wrong = w_dec_stored[3]                     # l'ancienne lecture (ligne)
    right = w_dec_stored.t()[3]                 # la lecture corrigee (feature)
    assert not torch.equal(wrong, right)
    # L'ancienne lecture levait IndexError des qu'un clamp_id depassait
    # d_model — les 32768 features ne tiennent pas dans 2048 lignes (reel).
    try:
        w_dec_stored[500]  # clamp_id > d_model=64 mais < d_sae
        raise AssertionError("d_model=64 doit refuser l'index 500")
    except IndexError:
        pass
