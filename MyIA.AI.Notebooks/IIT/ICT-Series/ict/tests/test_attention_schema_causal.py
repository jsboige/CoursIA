"""Tests du case 5bis (#15798) — axes causaux du schéma attentionnel.

Verite terrain synthetique : trois bras dont les clauses partagent le meme
contexte et portent des features SAE PLANTEES disjointes (bras A -> bloc 0,
bras B -> bloc 1, bras C -> bloc 2) sur un fond commun. Un patch de la
clause du donneur DOIT deplacer le centroide du receveur vers celui du
donneur ; le sham (write-back) doit etre l'identite ; le controle aleatoire
apparie doit deplacer moins ; l'interchange bilateral doit coincider avec le
patch unilateral (verrou de coherence du moteur).

Ce fichier epingle aussi les deux gardes structurelles du protocole :
l'ordre anti-HARKing (null AVANT les bras principaux, exige par fichier) et
la coherence inter-axes (meme fenetre de clause pour l'etat et le readout).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from ict import attention_schema_causal as asc  # noqa: E402

D_SAE = 3000
K_TOP = 12
BLOCK = 500          # taille d'un bloc plante (3 blocs + fond) — LARGE : la
# frequence d'un corpus de 9 prompts est quantifiee a {1,2,3,6}/9 ; chaque
# classe quantisee doit contenir assez de features de normes etalees pour que
# la bande (norme, frequence) du controle apparie ne soit jamais vide.
#: Amplitudes par feature, graduees et fixes : le controle apparie du moteur
#: exige des candidates dans la bande de norme de chaque cible — un univers
#: degeneré (blocs d'amplitude uniforme) n'offre aucune candidate hors cible.
_AMP = np.random.default_rng(12345).uniform(0.2, 1.0, D_SAE)
_BLOCKS = (np.arange(0, BLOCK), np.arange(BLOCK, 2 * BLOCK),
           np.arange(2 * BLOCK, 3 * BLOCK))
_BASELINE = np.arange(3 * BLOCK, D_SAE)
#: Banque graduee : la moitie du fond tire a l'ECHELLE CLAUSE dans exactement
#: UN contexte sur trois (meme masque pour tous les bras). Ces features ont
#: donc frequence 1/3 et normes a queue lourde — exactement le profil des
#: features de clause plantees — sans jamais contribuer au differentiel
#: inter-bras (contribution identique dans chaque bras, seul le diviseur
#: differe). Sans cette banque, la bande (norme +-50%, frequence +-50%) du
#: controle apparie est VIDE pour toute cible plantee : le fond ordinaire a
#: frequence 1.0 et norme ~10x plus faible.
_HI = _BASELINE[:len(_BASELINE) // 2]
_LO = _BASELINE[len(_BASELINE) // 2:]
_HI_CTX = {int(f): i % 3 for i, f in enumerate(_HI)}


def _entry(tokens, planted_block: int, *, seed: int, ctx: int):
    """Entry top-k d'un prompt : bloc plante fort + fond commun stable."""
    rng = np.random.default_rng(seed * 31 + ctx)
    T = len(tokens)
    ids = np.zeros((T, K_TOP), dtype=np.int32)
    vals = np.zeros((T, K_TOP), dtype=np.float32)
    planted = _BLOCKS[planted_block]
    hi = np.array([f for f in _HI if _HI_CTX[int(f)] == ctx % 3])
    for t in range(T):
        # Jitter borne : sans jitter le top-k est identique a chaque prompt et
        # la FREQUENCE est bimodale (1 ou 0) — aucun candidat n'entre jamais
        # dans la bande de frequence du controle apparie. Un jitter NON borne
        # (lognormal brut) a l'effet inverse : les normes passent en lottery de
        # tir maximal (queues a 1600+ qu'aucune candidate ne rejoint, freq
        # quantisee a 1/9 par gagnant unique). Le clip [0.5, 2] garde des
        # frequences graduees SANS queue de norme inappariable.
        if str(tokens[t]).startswith("§"):
            pool = planted
            j = np.clip(rng.lognormal(0.0, 0.6, size=pool.size), 0.5, 2.0)
            weights = _AMP[pool] * 12.0 * j
        else:
            pool = np.concatenate([hi, _LO])
            j = np.clip(rng.lognormal(0.0, 0.6, size=pool.size), 0.5, 2.0)
            # La banque graduee tire a l'echelle clause dans son contexte.
            w = _AMP[pool] * j
            w[:hi.size] *= 8.0
            weights = w
        top = np.argsort(weights)[::-1][:K_TOP]
        pick = pool[top]
        ids[t] = pick
        vals[t] = weights[top]
    return {"ids": ids, "vals": vals, "tokens": np.array(tokens)}


def _tokens(context: list[str], clause: list[str]) -> list[str]:
    """Marque les tokens de clause par § (verite terrain plantee : seules les
    positions de clause portent le bloc differentiel fort)."""
    return list(context) + [f"§{c}" for c in clause]


def _make_traces(arms: dict[str, list[str]], *, seed: int,
                 contexts: list[str]) -> dict:
    """Traces synthetiques au format exact du pipeline (meta + prompts)."""
    clauses = list(arms.values())
    prompts = {}
    for i, ctx in enumerate(contexts):
        ctx_tokens = [f"ctx{i}_{j}" for j in range(len(ctx.split()))]
        for name, clause in arms.items():
            cl_tokens = [f"cl_{name}_{j}" for j in range(len(clause.split()))]
            tokens = ctx_tokens + cl_tokens
            prompts[(name, i)] = _entry(
                _tokens(ctx_tokens, cl_tokens),
                # Les objets de calibration partagent le MEME bloc plante : la
                # paire neutre ne doit deplacer l'etat qu'au bruit pres (c'est
                # le sigma du null) — sinon le test mesure la verite terrain
                # synthetique au lieu de la garde anti-HARKing.
                {"attn_self": 0, "attn_other": 1, "obj_chaise": 2,
                 "calib_obj1": 0, "calib_obj2": 0}[name],
                seed=seed, ctx=i)
    return {
        "meta": {"d_sae": D_SAE, "k": K_TOP, "layer": 12, "seed": seed,
                 "model": "synthetic", "sae_repo": "synthetic",
                 "instrument": "sae"},
        "prompts": prompts,
    }


CONTEXTS = ["alpha beta gamma delta epsilon zeta eta theta iota kappa",
                 "lambda mu nu xi omicron pi rho sigma tau upsilon",
                 "phi chi psi omega un deux trois quatre cinq six"]


@pytest.fixture()
def main_traces_by_seed():
    arms = {
        "attn_self": "a b c d e",
        "attn_other": "d e f g h i",
        "obj_chaise": "h i j k l",
    }
    return {s: _make_traces(arms, seed=s, contexts=CONTEXTS) for s in (0, 1, 7, 42, 99)}


@pytest.fixture()
def calib_traces_by_seed():
    arms = {"calib_obj1": "j k", "calib_obj2": "l m n"}
    return {s: _make_traces(arms, seed=s, contexts=CONTEXTS) for s in (0, 1, 7, 42, 99)}


# --------------------------------------------------------------------------- #
# Fenetre causale
# --------------------------------------------------------------------------- #

def test_clause_divergence_at_first_difference():
    a = ["x", "y", "z", "u"]
    b = ["x", "y", "w", "v", "t"]
    assert asc.clause_divergence(a, b) == 2


def test_clause_divergence_prefix_contained():
    assert asc.clause_divergence(["x", "y"], ["x", "y", "z"]) == 2


def test_clause_divergence_identical_raises():
    with pytest.raises(ValueError, match="fenetre causale"):
        asc.clause_divergence(["x"], ["x"])


# --------------------------------------------------------------------------- #
# Selection de cible
# --------------------------------------------------------------------------- #

def test_pairwise_differential_picks_planted_features(main_traces_by_seed):
    traces = main_traces_by_seed[0]
    feats = asc.pairwise_differential(traces, "attn_self", "attn_other", k=8)
    # Les blocs plantes 0 et 1 dominent le differentiel de la paire.
    planted = set(range(0, 2 * BLOCK))
    assert set(int(f) for f in feats) <= planted
    assert feats.size == 8


def test_feature_profiles_shapes_and_freq_bounds(main_traces_by_seed):
    norms, freqs = asc.feature_profiles(main_traces_by_seed[0])
    assert norms.shape == (D_SAE,) and freqs.shape == (D_SAE,)
    assert freqs.max() <= 1.0 + 1e-9
    planted = asc.pairwise_differential(
        main_traces_by_seed[0], "attn_self", "attn_other", k=8)
    assert all(norms[f] > 0 for f in planted)


# --------------------------------------------------------------------------- #
# Axe ETAT : cible / sham / aleatoire apparie
# --------------------------------------------------------------------------- #

def test_state_patch_moves_centroid_toward_donor(main_traces_by_seed):
    fx = asc.state_intervention_effects(
        main_traces_by_seed[0], "attn_self", "attn_other", 1)
    assert fx.cos_target > fx.cos_before + 0.2   # deplacement dirige fort
    assert fx.cos_target > fx.cos_random          # ...plus que le controle
    assert fx.interchange_coherent                # verrou moteur


def test_state_sham_is_identity(main_traces_by_seed):
    fx = asc.state_intervention_effects(
        main_traces_by_seed[0], "attn_self", "obj_chaise", 2)
    assert abs(fx.cos_sham - fx.cos_before) < 1e-9


def test_state_random_control_moves_less_than_target(main_traces_by_seed):
    for seed in (0, 7):
        fx = asc.state_intervention_effects(
            main_traces_by_seed[seed], "attn_other", "obj_chaise", 0)
        assert (fx.cos_target - fx.cos_before) > (fx.cos_random - fx.cos_before)


def test_state_damage_is_selective_by_construction(main_traces_by_seed):
    fx = asc.state_intervention_effects(
        main_traces_by_seed[0], "attn_self", "attn_other", 0)
    # Le patch n'ecrit QUE positions x features cibles : hors-cible exactement 0.
    assert fx.damage["off_target_rel"] == pytest.approx(0.0, abs=1e-12)
    assert fx.selectivity == "selective"


# --------------------------------------------------------------------------- #
# Axe READOUT
# --------------------------------------------------------------------------- #

def test_readout_signature_migrates_toward_donor(main_traces_by_seed):
    ro = asc.readout_axis(
        main_traces_by_seed[0], "attn_self", "attn_other", 1)
    assert ro["jaccard_shift"] > 0
    assert 0.0 <= ro["consumer_hit_rate_before"] <= 1.0
    assert -1.0 <= ro["consumer_hit_shift"] <= 1.0


def test_readout_seed_recorded_for_by_seed_aggregation(main_traces_by_seed):
    ro = asc.readout_axis(main_traces_by_seed[7], "attn_self", "attn_other", 0)
    assert ro["seed"] == 7


# --------------------------------------------------------------------------- #
# Axe COMPORTEMENT : fonctions pures
# --------------------------------------------------------------------------- #

def test_classify_target_each_arm():
    assert asc.classify_target("Mon attention porte sur la table.") == "attn_self"
    assert asc.classify_target("L'agent Y décrit son attention.") == "attn_other"
    assert asc.classify_target("La chaise en bois est posée.") == "obj_chaise"


def test_classify_target_ambiguous_and_none():
    assert asc.classify_target("mon attention et la chaise posée") == "ambiguous"
    assert asc.classify_target("Le carnet est ouvert sur la table.") == "none"


def test_classify_target_normalizes_typography():
    assert asc.classify_target("Mon  attention   porte.") == "attn_self"
    assert asc.classify_target("L’agent Y regarde.") == "attn_other"


def test_marker_logit_gap_sign():
    logits = np.zeros(100, dtype=np.float32)
    logits[12], logits[77] = 2.0, -1.0
    assert asc.marker_logit_gap(logits, 12, 77) == pytest.approx(3.0)


# --------------------------------------------------------------------------- #
# Verdict PAR AXE
# --------------------------------------------------------------------------- #

def test_axis_verdict_supported():
    v, kills = asc.axis_verdict([0.5, 0.6, 0.4, 0.7, 0.5], [0.0] * 5, 0.1)
    assert v == "SUPPORTED" and kills == []


def test_axis_verdict_not_supported_when_control_equal():
    v, _ = asc.axis_verdict([0.5, 0.6, 0.4, 0.7, 0.5],
                            [0.5, 0.6, 0.4, 0.7, 0.5], 0.1)
    assert v == "NOT_SUPPORTED"


def test_axis_verdict_inconclusive_when_inconsistent():
    v, kills = asc.axis_verdict([0.5, -0.1, 0.4, -0.2, 0.5],
                                [0.0] * 5, 0.1)
    assert v == "INCONCLUSIF" and kills


def test_axis_verdict_rejects_mismatched_lengths():
    with pytest.raises(ValueError, match="appari"):
        asc.axis_verdict([0.1, 0.2], [0.0], 0.05)


# --------------------------------------------------------------------------- #
# Null anti-HARKing + runner end-to-end (synthetique)
# --------------------------------------------------------------------------- #

def test_calibrate_null_sigmas_positive(calib_traces_by_seed):
    null = asc.calibrate_null(calib_traces_by_seed)
    assert null.sigma_state >= 0.0
    assert len(null.state_shift_by_seed) == 5
    assert len(null.readout_shift_by_seed) == 5


def test_calibrate_null_refuses_degenerate_pool(calib_traces_by_seed):
    with pytest.raises(ValueError, match="null invalide"):
        asc.calibrate_null({0: calib_traces_by_seed[0]})


def test_run_traces_axes_end_to_end(main_traces_by_seed, calib_traces_by_seed,
                                    tmp_path):
    null = asc.calibrate_null(calib_traces_by_seed)
    result = asc.run_traces_axes(null, main_traces_by_seed)
    assert set(result) >= {"case", "prediction", "null", "axes", "behavior"}
    # 6 directions x 2 axes = 12 entrees de verdict, chacune bien formee.
    assert len(result["axes"]) == 12
    for key, axis in result["axes"].items():
        assert axis["verdict"] in ("SUPPORTED", "NOT_SUPPORTED", "INCONCLUSIF"), key
        assert axis["epsilon"] is not None
    assert result["behavior"]["verdict"] == "PENDING"
    # La paire critique AST doit etre presente.
    assert "etat:attn_self<-attn_other" in result["axes"]
    # Sur la verite terrain synthetique, l'axe etat de la paire critique
    # DOIT etre SUPPORTED (deplacement dirige plante par construction).
    assert result["axes"]["etat:attn_self<-attn_other"]["verdict"] == "SUPPORTED"
    assert result["axes"]["etat:attn_self<-attn_other"]["interchange_coherent_all"]


def test_cli_requires_null_file_before_run(tmp_path):
    """L'ordre anti-HARKing est impossible a inverser : run sans null echoue."""
    # Le fichier null absent : la lecture echoue AVANT tout score principal.
    with pytest.raises(FileNotFoundError):
        asc._cli(["run", "whatever.npz", "--null",
                  str(tmp_path / "absent.json"),
                  "--out", str(tmp_path / "r.json")])
    assert not (tmp_path / "r.json").exists()


def test_cli_null_then_run_roundtrip(main_traces_by_seed, calib_traces_by_seed,
                                     tmp_path):
    """Roundtrip complet : null -> JSON gele -> run qui le consomme."""

    def _save(traces, p):
        arrays = {}
        for (name, i), e in traces["prompts"].items():
            arrays[f"{name}__{i}__topk_ids"] = e["ids"]
            arrays[f"{name}__{i}__topk_vals"] = e["vals"].astype(np.float16)
            arrays[f"{name}__{i}__tokens"] = e["tokens"]
        meta = dict(traces["meta"])
        meta["prompt_sets"] = sorted({k[0] for k in traces["prompts"]})
        meta["variant"] = "trained"
        meta["contract_version"] = "v1.0.0"
        meta["schema"] = "sparse_topk_v1"
        arrays["__meta__"] = json.dumps(meta)
        np.savez(p, **arrays)

    calib_paths = []
    for seed, traces in sorted(calib_traces_by_seed.items()):
        p = tmp_path / f"calib_{seed}.npz"
        _save(traces, p)
        calib_paths.append(str(p))

    null_path = tmp_path / "null.json"
    asc._cli(["null"] + calib_paths + ["--out", str(null_path)])
    frozen = json.loads(null_path.read_text(encoding="utf-8"))
    assert "sigma_state" in frozen and "sigma_readout" in frozen

    main_paths = []
    for seed, traces in sorted(main_traces_by_seed.items()):
        p = tmp_path / f"main_{seed}.npz"
        _save(traces, p)
        main_paths.append(str(p))

    out_path = tmp_path / "result.json"
    asc._cli(["run"] + main_paths + ["--null", str(null_path),
                                     "--out", str(out_path)])
    result = json.loads(out_path.read_text(encoding="utf-8"))
    assert result["case"] == "case5bis_attention_schema_causal"
    assert len(result["axes"]) == 12


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
