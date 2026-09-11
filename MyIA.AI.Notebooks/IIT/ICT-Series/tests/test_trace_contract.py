"""Tests du contrat de trace v1 (#15476).

Couvre les 4 axes du ticket :

1. **validate_manifest** : valide les champs obligatoires et optionnels,
   respecte la retro-compatibilite par defaut et refuse les manifestes
   incomplets en strict.
2. **enforce_instrument** : mechanisme central de l'acceptance #1 -- un
   chargeur SAE refuse une trace J-Lens, et vice-versa.
3. **check_alignment** : diagnostique actionnable sur les mismatches
   (acceptance #2).
4. **topk_semantics** : asymetrie SAE=exact_zero / J-Lens=unobserved
   (acceptance #3).

Les tests utilisent **uniquement** la stdlib + numpy. Le pattern est
identique a :mod:`ict.tests.test_sae_traces` / :mod:`ict.tests.test_jlens_traces`
du meme package (cf. script dedie ``detect_consecutive_code_cells.py``).

Auto-test
---------
    python tests/test_trace_contract.py            # verbose
    python tests/test_trace_contract.py --quiet    # que les failures
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

# Permet l'import du package `ict` depuis la racine de la serie.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from ict.trace_contract import (  # noqa: E402
    ALIGNMENT_KEYS,
    CONTRACT_VERSION,
    INSTRUMENTS,
    OPTIONAL_META_KEYS,
    REQUIRED_META_KEYS,
    TOPK_EXACT_ZERO,
    TOPK_UNOBSERVED,
    TraceContractError,
    build_manifest,
    check_alignment,
    enforce_instrument,
    topk_semantics,
    validate_manifest,
)


# --------------------------------------------------------------------------- #
# Tests de validate_manifest
# --------------------------------------------------------------------------- #
def test_validate_manifest_minimal_sae_ok():
    """Manifeste minimal (REQUIRED_META_KEYS seulement) + instrument SAE : OK."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16)
    m_out = validate_manifest(m)
    assert m_out["contract_version"] == CONTRACT_VERSION
    assert m_out["instrument"] == "sae"
    assert m_out["schema"] == "<set>__<idx>__<field>"


def test_validate_manifest_minimal_jlens_ok():
    """Idem pour J-Lens : manifeste minimal valide, instrument discriminant."""
    m = build_manifest("jlens", d_model=4096, k=50, layer=16)
    m_out = validate_manifest(m)
    assert m_out["instrument"] == "jlens"


def test_validate_manifest_strict_refuses_legacy_minimal():
    """En strict, OPTIONAL_META_KEYS obligatoire -- un manifeste minimal echoue."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16)  # que REQUIRED
    try:
        validate_manifest(m, strict=True)
    except TraceContractError as e:
        assert "champs stricts manquants" in str(e)
        return
    raise AssertionError("validate_manifest(strict=True) aurait dû refuser")


def test_validate_manifest_strict_accepts_full():
    """En strict, un manifeste complet passe."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16,
                       model="Qwen3.5-9B-Base", model_revision="abc123",
                       model_family="qwen", run="run-42", seed=42,
                       prompt_set="structure",
                       capture_point="decoder_layer_16_resid",
                       module="decoder",
                       tensor_space="resid_post",
                       dtype="bfloat16", device="cuda:0",
                       schema_version="v1.0.0",
                       sae_repo="Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50",
                       sae_k=50,
                       # Champs neutres pour instrument=sae : la presence
                       # suffit, pas la valeur (zero / vide).
                       lens_repo="", lens_kind="", lens_rank=0,
                       n_clamp=0, prompt_input_hash="abc123")
    m_out = validate_manifest(m, strict=True)
    assert m_out["model"] == "Qwen3.5-9B-Base"


def test_validate_manifest_legacy_lens_sae_is_accepted():
    """Retro-compat : meta['lens']='sae' sans meta['instrument'] -> instrument='sae'."""
    m = {"d_model": 4096, "k": 50, "layer": 16, "lens": "sae"}
    m_out = validate_manifest(m)
    assert m_out["instrument"] == "sae"


def test_validate_manifest_legacy_lens_jacobian_is_jlens():
    """Retro-compat : meta['lens']='jacobian' -> instrument='jlens'."""
    m = {"d_model": 4096, "k": 50, "layer": 16, "lens": "jacobian"}
    m_out = validate_manifest(m)
    assert m_out["instrument"] == "jlens"


def test_validate_manifest_unknown_instrument_refused():
    """Un instrument hors enum (ex: 'foo') est REFUSE meme en non-strict."""
    m = {"d_model": 4096, "k": 50, "layer": 16, "instrument": "foo"}
    try:
        validate_manifest(m)
    except TraceContractError as e:
        assert "hors enum" in str(e)
        return
    raise AssertionError("validate_manifest aurait dû refuser instrument='foo'")


def test_validate_manifest_missing_required_refused():
    """Un manifeste sans un champ REQUIRED est REFUSE."""
    m = {"instrument": "sae", "d_model": 4096, "layer": 16}  # pas de 'k'
    try:
        validate_manifest(m)
    except TraceContractError as e:
        assert "obligatoires manquants" in str(e)
        assert "'k'" in str(e)
        return
    raise AssertionError("validate_manifest aurait dû refuser sans 'k'")


def test_validate_manifest_non_dict_raises():
    """Un manifeste qui n'est pas un dict (ex: str, int) leve."""
    try:
        validate_manifest("pas un dict")
    except TraceContractError as e:
        assert "au lieu de dict" in str(e)
        return
    raise AssertionError("validate_manifest aurait dû refuser un str")


def test_validate_manifest_v2x_is_refused():
    """Un manifeste v2.x est REFUSE par le chargeur v1 (migration explicite)."""
    m = {"contract_version": "v2.0.0", "instrument": "sae",
         "d_model": 4096, "k": 50, "layer": 16}
    try:
        validate_manifest(m)
    except TraceContractError as e:
        assert "non supportee" in str(e)
        return
    raise AssertionError("validate_manifest aurait dû refuser contract_version='v2.0.0'")


def test_validate_manifest_v1_x_y_is_accepted():
    """Un manifeste v1.x.y (x>0) est accepte par le chargeur v1."""
    m = {"contract_version": "v1.3.7", "instrument": "sae",
         "d_model": 4096, "k": 50, "layer": 16}
    m_out = validate_manifest(m)
    assert m_out["contract_version"] == "v1.3.7"


# --------------------------------------------------------------------------- #
# Tests de enforce_instrument (acceptance #1)
# --------------------------------------------------------------------------- #
def test_enforce_instrument_sae_passes_for_sae_manifest():
    """Manifeste SAE -> enforce('sae') : OK."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16)
    enforce_instrument(m, "sae")  # pas d'exception


def test_enforce_instrument_sae_refuses_jlens_manifest():
    """Manifeste J-Lens -> enforce('sae') : REFUSE avec diagnostic."""
    m = build_manifest("jlens", d_model=4096, k=50, layer=16)
    try:
        enforce_instrument(m, "sae")
    except TraceContractError as e:
        msg = str(e)
        assert "instrument=" in msg and "jlens" in msg
        assert "attendu=" in msg and "sae" in msg
        return
    raise AssertionError("enforce_instrument aurait dû refuser instrument='jlens'")


def test_enforce_instrument_unknown_raises():
    """enforce avec expected hors enum leve."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16)
    try:
        enforce_instrument(m, "foo")
    except TraceContractError:
        return
    raise AssertionError("enforce_instrument aurait dû refuser expected='foo'")


def test_enforce_instrument_legacy_sae_passes():
    """Retro-compat : manifeste sans instrument mais avec lens='sae' + enforce('sae')."""
    m = {"d_model": 4096, "k": 50, "layer": 16, "lens": "sae"}
    enforce_instrument(m, "sae")  # pas d'exception


def test_enforce_instrument_legacy_jacobian_passes():
    """Retro-compat : lens='jacobian' + enforce('jlens')."""
    m = {"d_model": 4096, "k": 50, "layer": 16, "lens": "jacobian"}
    enforce_instrument(m, "jlens")  # pas d'exception


def test_enforce_instrument_no_metadata_refused():
    """Sans instrument ni lens legacy, enforce refuse meme en non-strict (anti-melange)."""
    m = {"d_model": 4096, "k": 50, "layer": 16}
    try:
        enforce_instrument(m, "sae")
    except TraceContractError as e:
        assert "Migration requise" in str(e)
        return
    raise AssertionError("enforce_instrument aurait dû refuser un manifeste nu")


# --------------------------------------------------------------------------- #
# Tests de check_alignment (acceptance #2)
# --------------------------------------------------------------------------- #
def test_check_alignment_identical_returns_empty():
    """Deux manifestes identiques (apres validate_manifest) -> 0 diff."""
    m_a = build_manifest("sae", d_model=4096, k=50, layer=16,
                         model="X", model_revision="abc", model_family="qwen",
                         dtype="bf16", run="r", seed=1, prompt_set="s")
    # Le contrat exige validate_manifest avant check_alignment (ajoute
    # contract_version + schema).
    m_a = validate_manifest(m_a)
    diffs = check_alignment(m_a, m_a)
    assert diffs == [], f"manifestes identiques, diffs={diffs}"


def test_check_alignment_layer_mismatch_is_diagnosed():
    """Mismatched layer -> diagnostic explicite."""
    m_a = build_manifest("sae", d_model=4096, k=50, layer=16)
    m_b = build_manifest("sae", d_model=4096, k=50, layer=24)
    m_a, m_b = validate_manifest(m_a), validate_manifest(m_b)
    diffs = check_alignment(m_a, m_b)
    assert any("layer" in d and "16" in d and "24" in d for d in diffs), diffs


def test_check_alignment_model_mismatch():
    """Mismatch modele -> diagnostic explicite."""
    m_a = build_manifest("sae", d_model=4096, k=50, layer=16, model="Qwen3.5-9B-Base")
    m_b = build_manifest("sae", d_model=2048, k=50, layer=12, model="Qwen3.5-2B-Base")
    m_a, m_b = validate_manifest(m_a), validate_manifest(m_b)
    diffs = check_alignment(m_a, m_b)
    layer_diffs = [d for d in diffs if "model" in d]
    d_sae_diffs = [d for d in diffs if "d_sae" in d]
    layer_d = [d for d in diffs if "layer" in d]
    assert layer_diffs, f"pas de diff model dans {diffs}"
    assert d_sae_diffs, f"pas de diff d_sae dans {diffs}"
    assert layer_d, f"pas de diff layer dans {diffs}"


def test_check_alignment_missing_field_on_a():
    """Champ present cote B mais absent cote A -> diagnostic 'absent cote A'."""
    m_a = build_manifest("sae", d_model=4096, k=50, layer=16)
    m_b = build_manifest("sae", d_model=4096, k=50, layer=16, model="X")
    m_a, m_b = validate_manifest(m_a), validate_manifest(m_b)
    diffs = check_alignment(m_a, m_b)
    assert any("model" in d and "absent cote A" in d for d in diffs), diffs


def test_check_alignment_diffs_format_is_actionnable():
    """Format des diffs : 'champ: 'valeur_a' != 'valeur_b'' -- actionable."""
    m_a = build_manifest("sae", d_model=4096, k=50, layer=16, seed=1)
    m_b = build_manifest("sae", d_model=4096, k=50, layer=16, seed=2)
    m_a, m_b = validate_manifest(m_a), validate_manifest(m_b)
    diffs = check_alignment(m_a, m_b)
    assert any(d == "seed: 1 != 2" for d in diffs), diffs


def test_check_alignment_subkeys():
    """Le parametre ``keys`` permet de restreindre l'alignement a un sous-ensemble."""
    m_a = build_manifest("sae", d_model=4096, k=50, layer=16, seed=1)
    m_b = build_manifest("sae", d_model=4096, k=50, layer=16, seed=2)
    m_a, m_b = validate_manifest(m_a), validate_manifest(m_b)
    diffs = check_alignment(m_a, m_b, keys=("layer",))
    assert diffs == []  # layer egaux, seul seed diff mais on l'ignore


# --------------------------------------------------------------------------- #
# Tests de topk_semantics (acceptance #3)
# --------------------------------------------------------------------------- #
def test_topk_semantics_sae_is_exact_zero():
    """SAE top-k : feature absente du top-k = activation EXACTEMENT nulle."""
    assert topk_semantics("sae") == TOPK_EXACT_ZERO


def test_topk_semantics_jlens_is_unobserved():
    """J-Lens top-k : identifiant absent du top-k = valeur NON OBSERVEE."""
    assert topk_semantics("jlens") == TOPK_UNOBSERVED


def test_topk_semantics_unknown_raises():
    """Instrument hors enum leve -- pas de semantique par defaut."""
    try:
        topk_semantics("foo")
    except TraceContractError:
        return
    raise AssertionError("topk_semantics aurait dû refuser 'foo'")


# --------------------------------------------------------------------------- #
# Tests de build_manifest (constructeur)
# --------------------------------------------------------------------------- #
def test_build_manifest_sae_minimal():
    """build_manifest('sae', d_model, k, layer) produit un manifeste complet."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16)
    assert m["contract_version"] == CONTRACT_VERSION
    assert m["instrument"] == "sae"
    assert m["d_model"] == 4096
    assert m["k"] == 50
    assert m["layer"] == 16


def test_build_manifest_passes_extra_keys():
    """Les **extra sont poses tels quels sur le manifeste."""
    m = build_manifest("sae", d_model=4096, k=50, layer=16,
                       sae_repo="Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50",
                       sae_k=50)
    assert m["sae_repo"].startswith("Qwen/")
    assert m["sae_k"] == 50


def test_build_manifest_rejects_unknown_instrument():
    """build_manifest refuse un instrument hors enum avant meme validate."""
    try:
        build_manifest("foo", d_model=4096, k=50, layer=16)
    except TraceContractError:
        return
    raise AssertionError("build_manifest aurait dû refuser 'foo'")


# --------------------------------------------------------------------------- #
# Tests d'integration : le contrat borne reellement le systeme
# --------------------------------------------------------------------------- #
def test_end_to_end_sae_loader_refuses_jlens_trace():
    """Integration : sae_traces.load_traces refuse une trace J-Lens."""
    import json
    import tempfile

    arrays = {
        "__meta__": np.array(json.dumps({
            "contract_version": "v1.0.0", "instrument": "jlens",
            "d_model": 4096, "k": 50, "layer": 16,
        })),
        "A__0__topk_ids": np.array([[0, 1, 2]], dtype=np.int32),
        "A__0__topk_vals": np.array([[0.1, 0.2, 0.3]], dtype=np.float32),
        "A__0__tokens": np.array(["tok"], dtype=str),
    }
    with tempfile.NamedTemporaryFile(suffix=".npz", delete=False) as f:
        np.savez_compressed(f, **arrays)
        path = f.name

    from ict import sae_traces
    try:
        sae_traces.load_traces(path)
    except TraceContractError as e:
        assert "attendu='sae'" in str(e)
        return
    raise AssertionError("sae_traces.load_traces aurait dû refuser la trace J-Lens")


def test_end_to_end_jlens_loader_refuses_sae_trace():
    """Integration : jlens_traces.load_traces refuse une trace SAE."""
    import json
    import tempfile

    arrays = {
        "__meta__": np.array(json.dumps({
            "contract_version": "v1.0.0", "instrument": "sae",
            "d_model": 4096, "k": 50, "layer": 16,
        })),
        "A__0__topk_ids": np.array([[0, 1, 2]], dtype=np.int32),
        "A__0__topk_vals": np.array([[0.1, 0.2, 0.3]], dtype=np.float32),
        "A__0__tokens": np.array(["tok"], dtype=str),
    }
    with tempfile.NamedTemporaryFile(suffix=".npz", delete=False) as f:
        np.savez_compressed(f, **arrays)
        path = f.name

    from ict import jlens_traces
    try:
        jlens_traces.load_traces(path)
    except TraceContractError as e:
        assert "attendu='jlens'" in str(e)
        return
    raise AssertionError("jlens_traces.load_traces aurait dû refuser la trace SAE")


def test_end_to_end_alignment_real_pair():
    """Integration : check_alignment entre deux manifestes realistes de run distinct."""
    m_run1 = build_manifest("sae", d_model=4096, k=50, layer=16,
                            model="Qwen3.5-9B-Base", model_revision="abc",
                            model_family="qwen", dtype="bfloat16",
                            run="run-1", seed=42, prompt_set="structure")
    m_run2 = build_manifest("sae", d_model=4096, k=50, layer=16,
                            model="Qwen3.5-9B-Base", model_revision="abc",
                            model_family="qwen", dtype="bfloat16",
                            run="run-2", seed=42, prompt_set="structure")
    m_run1, m_run2 = validate_manifest(m_run1), validate_manifest(m_run2)
    diffs = check_alignment(m_run1, m_run2)
    # seul 'run' doit differ
    assert diffs == ["run: 'run-1' != 'run-2'"], diffs


# --------------------------------------------------------------------------- #
# Runner stdlib (sans pytest)
# --------------------------------------------------------------------------- #
def _run_all():
    import unittest

    # Regroupe les fonctions test_* dans une TestCase factice en les
    # attachant comme methodes statiques (les TestCase methodes prennent
    # `self`, on l'ignore en passant par ``staticmethod`` qui les transforme
    # en methodes sans args).
    test_funcs = [
        (name, obj) for name, obj in globals().items()
        if name.startswith("test_") and callable(obj)
    ]

    class _DynamicContractTests(unittest.TestCase):
        pass

    for name, fn in test_funcs:
        # On attache en tant qu'attribut de classe (unittest les voit
        # comme des methodes, mais elles sont en fait des fonctions
        # statiques). Le runner les appelle sans self.
        setattr(_DynamicContractTests, name, staticmethod(fn))

    loader = unittest.TestLoader()
    suite = loader.loadTestsFromTestCase(_DynamicContractTests)
    runner = unittest.TextTestRunner(
        verbosity=2 if "--quiet" not in sys.argv else 0)
    return runner.run(suite)


if __name__ == "__main__":
    result = _run_all()
    sys.exit(0 if result.wasSuccessful()
             else len(result.failures) + len(result.errors))
